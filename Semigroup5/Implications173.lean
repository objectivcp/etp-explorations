import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation316_4512_implies_Equation41640 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41640 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (x ◇ z))]

theorem Equation4512_41640_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41640 : Equation41640 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK1]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41640 (sK1 ◇ (sK1 ◇ sK1)) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41640 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l6 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41640 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (X0 ◇ X1))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2, 2]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41640 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l13 sK1]
  have l15 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41640 X0 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← h41640 sK1 X0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41640 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41640 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1, 2]; rw [h41640 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l8 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [h41640 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 (sK1 ◇ sK1) sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l18 sK1]
  have l22 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l15 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1, 2]; rw [← l13 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [← l21 sK1]
  have l25 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l22 X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1]
  have l26 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l25 X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l23 sK1]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41640 (sK0 ◇ sK0) X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK0 sK1]
    conv => enter [1]; rw [← l26 (sK1 ◇ (sK1 ◇ sK1)) sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41640 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h41640 sK0 (sK0 ◇ sK0) sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l32 x y]
  conv => enter [1]; rw [l27 y]

theorem Equation316_4512_implies_Equation41641 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41641 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (x ◇ w))]

theorem Equation4512_41641_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41641 : Equation41641 G) : Equation316 G := by
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
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l5 sK1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41641 (sK1 ◇ sK1) X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41641 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l12 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41641 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l13 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41641 sK1 X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l7 sK1 X0]
  have l14 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41641 (sK1 ◇ sK1) X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [l9 sK1 X0]
  have l15 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41641 X0 sK1 sK1 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l16 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l15 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l17 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41641 (sK1 ◇ (sK1 ◇ sK1)) sK1 (sK1 ◇ sK1) sK1]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41641 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1 sK1]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41641 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l20 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 X1 X0]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l17 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1 sK1 sK1]
    conv => enter [1]; rw [← l20 sK1 sK1 sK1]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l22 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l18 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [← l16 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l26 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l25 sK1 X0]
    conv => enter [1]; rw [← l21 sK1]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l26 sK1 X0]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l23 sK1]
  have l29 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41641 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1]; rw [← l27 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l30 x y]
  conv => enter [1]; rw [l28 y]

@[equational_result]
theorem Equation316_implies_Equation41643 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41643 G := by
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
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_41643_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41643 : Equation41643 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41643 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41643 X0 X0 X0]
    conv => enter [1]; rw [← h41643 X1 X0 X0]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l10 X0 sK1]
    conv => enter [1]; rw [← l13 sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l15 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation316_4512_implies_Equation41644 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41644 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (y ◇ z))]

theorem Equation4512_41644_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41644 : Equation41644 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41644 X0 X0 X0]
    conv => enter [1]; rw [← h41644 X1 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ X1 X2 sK1 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l6 X1 X1 X2]
    conv => enter [1]; rw [l5 X1 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l8 sK1 sK1]
  have l11 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41644 X1 X1 X2]
    conv => enter [1]; rw [l5 X1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l11 X1 sK0 sK0]
    conv => enter [1, 2]; rw [l9 X1 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation316_4512_implies_Equation41645 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41645 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (y ◇ w))]

theorem Equation4512_41645_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41645 : Equation41645 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41645 X1 X2 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41645 X0 X2 X2 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41645 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41645 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation316_4512_implies_Equation41647 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41647 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (z ◇ y))]

theorem Equation4512_41647_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41647 : Equation41647 G) : Equation316 G := by
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
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41647 X0 X0 X0]
    conv => enter [1]; rw [← h41647 X1 X0 X0]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41647 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l10 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l9 (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l6 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l13 sK1 sK1]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l9 X0 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1, 2]; rw [l9 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l3 sK1 X0]
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1, 2, 1]; rw [l9 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1, 1]; rw [l9 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l16 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l21 sK1 X0 sK0]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41647 X0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK1]
  have l26 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l25 X0 sK1]
    conv => enter [1]; rw [l3 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l27 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l26 X0 sK1]
    conv => enter [1]; rw [← l24 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l28 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l27 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l11 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l29 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l28 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK1]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l29 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK1]
  have l31 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l30 X0 X0 sK1]
    conv => enter [1]; rw [← l23 sK1 X0]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l32 sK1]
  intro x y
  conv => enter [1]; rw [l33 x y]

@[equational_result]
theorem Equation316_implies_Equation41648 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41648 G := by
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
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← h316 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK1 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_41648_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41648 : Equation41648 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41648 X0 X0 X0]
    conv => enter [1]; rw [← h41648 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41648 sK0 X0 X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 sK0 X1]
    conv => enter [1]; rw [l2 sK0 (X1 ◇ (X1 ◇ X1)) sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1]
    conv => enter [1, 2]; rw [l2 X1 X1 sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 X1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1, 1]; rw [l0 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation316_4512_implies_Equation41649 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41649 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (z ◇ w))]

theorem Equation4512_41649_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41649 X1 X2 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41649 X0 X2 X2 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation316_4512_implies_Equation41651 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41651 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (w ◇ y))]

theorem Equation4512_41651_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41651 : Equation41651 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41651 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41651 X0 X1 X1 X1]
  have l3 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41651 X0 sK1 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l6 X0 sK1]
    conv => enter [1]; rw [← l5 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l8 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation316_4512_implies_Equation41652 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41652 G := by
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
  conv => enter [1]; rw [l10 x y (z ◇ (w ◇ z))]

theorem Equation4512_41652_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41652 : Equation41652 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41652 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41652 X0 X1 X1 X1]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l6 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l9 sK1 sK1]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41652 X0 X1 X2 X2]
    conv => enter [1, 2, 2, 2]; rw [l6 X2 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l6 X0 sK0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41652 X0 (X1 ◇ (X2 ◇ X1)) X1 X2]
    conv => enter [1, 2]; rw [l6 (X1 ◇ (X2 ◇ X1)) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X1) (sK0 ◇ sK0)]
  have l18 : ∀ X0 sK0 X2 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l11 X0 X0 X2 sK0]
    conv => enter [1]; rw [l12 X0 (X2 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l20 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l17 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 (sK0 ◇ sK0)]
  have l21 : ∀ sK1 sK0 X2 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l18 sK1 sK0 X2]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l23 : ∀ sK1 X1 X2 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X1 X2 sK0
    conv => enter [1]; rw [l20 sK1 X1 X2 sK0]
  have l24 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l21 sK0 sK0 X2]
  have l25 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l23 sK0 X1 X2 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ sK0) sK1]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK0]
  have l29 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41652 X0 (X1 ◇ X2) sK0 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l30 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l29 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l30 X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l28 sK0]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l31 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 X0 X1]
  have l33 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l32 sK1 X1 sK0]
  have l34 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l33 sK0 X1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l22 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l35 x y]

@[equational_result]
theorem Equation316_implies_Equation41653 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41653 G := by
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
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_41653_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41653 : Equation41653 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41653 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41653 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h41653 X0 (X1 ◇ (X2 ◇ X2)) X1 X2]
    conv => enter [1, 2]; rw [l1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l15 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l14 X0 X1 X2 sK1]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X2) (sK1 ◇ sK1)]
  have l16 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l15 X0 X1 X2 sK1]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (sK1 ◇ sK1)]
  have l17 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l16 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [l10 X0 (sK1 ◇ sK1) sK0]
  have l18 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l17 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 X0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 X0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l20 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l19 sK1 X1 sK0]
  have l21 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l20 sK0 X1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation316_4512_implies_Equation41654 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41654 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l4 sK2 sK2 sK2]
    conv => enter [1]; rw [← l3 X2 sK2 sK2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l5 sK2 X2]
    conv => enter [1]; rw [l1 X2 X2 sK2]
  have l8 : ∀ X0 X2 sK2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK2]
  have l9 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK2 sK2]
  have l10 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l9 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z w u
  conv => enter [1]; rw [l10 x y (z ◇ (w ◇ u))]

theorem Equation4512_41654_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41654 : Equation41654 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41654 X1 X2 X2 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41654 X0 X2 X1 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41654 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41654 X1 X0 X0 X0 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation316_4512_implies_Equation41656 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41656 G := by
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
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [l13 sK0 sK0 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation4512_41656_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41656 : Equation41656 G) : Equation316 G := by
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
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41656 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 X0]
  have l12 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41656 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41656 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41656 (sK1 ◇ sK1) X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l10 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1, 2, 2]; rw [l10 sK1 X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l11 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1, 2]; rw [l3 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l19 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l17 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l20 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1 sK1]
    conv => enter [1]; rw [← h41656 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l21 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← l12 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l20 sK1]
  have l23 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41656 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l21 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41656 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l24 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41656 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l25 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l28 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l26 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l26 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l30 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l28 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l31 sK1]
  have l33 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41656 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK1]
  have l34 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l33 sK1 X0]
    conv => enter [1, 2, 2]; rw [l6 sK1]
  have l35 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l34 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l24 sK1]
  have l36 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [l35 sK1 X0]
  have l37 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [l36 sK1 X0]
  have l38 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h41656 (sK1 ◇ (sK1 ◇ sK1)) X0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [← l16 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l39 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41656 X0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1 X0]
  have l40 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l39 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) X0 (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l41 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [l38 sK1 X0]
  have l42 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l40 X0 sK1 X1]
    conv => enter [1, 1]; rw [← l32 sK1]
  have l43 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l42 X0 sK1 X1]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK1 X0]
  have l44 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l43 X0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l41 sK1 X0]
  have l45 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l44 X0 sK1]
    conv => enter [1]; rw [← l37 sK1 X0]
  intro x y
  conv => enter [1]; rw [l45 x y]
  conv => enter [1]; rw [l32 y]

theorem Equation316_4512_implies_Equation41657 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41657 G := by
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
  have l13 : ∀ X0 X2 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l12 sK0 X0 X2]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [← l13 sK0 sK2 sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation4512_41657_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41657 : Equation41657 G) : Equation316 G := by
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
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41657 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41657 X1 X2 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41657 X0 X1 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41657 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41657 X0 (X0 ◇ X0) X0]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ X0)]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41657 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41657 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41657 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X0)]
  have l14 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK1) sK1]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK0]
  have l18 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l13 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l7 X0 X1]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X0 X1]
    conv => enter [1]; rw [← h41657 X1 X0 X1]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l16 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l23 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l25 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l24 sK1]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l25 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [← l26 sK1]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]
  conv => enter [1]; rw [l27 y]

theorem Equation316_4512_implies_Equation41658 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41658 G := by
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
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [l13 sK1 sK1 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41658_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41658 : Equation41658 G) : Equation316 G := by
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
  have l5 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h41658 sK0 X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41658 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h41658 sK0 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41658 sK1 X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l9 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l8 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l2 sK1 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK0 sK0 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK0 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation316_implies_Equation41660 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41660 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK1]
  have l5 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l7 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l5 sK1 X1 sK1 sK0]
  have l8 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l7 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_41660_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41660 : Equation41660 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h41660 (X2 ◇ X2) X0 X1]
    conv => enter [1]; rw [h41660 (X2 ◇ X2) X2 X3]
    conv => enter [1, 2, 2]; rw [h41660 (X2 ◇ X2) X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h41660 X1 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h41660 (X0 ◇ X0) X0 X1]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41660 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41660 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41660 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l3 sK1 (X0 ◇ X0)]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1]; rw [← h41660 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← h41660 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [← h41660 (X0 ◇ X0) X0 X0]
  have l14 : ∀ X2 X3 : G, (X2 ◇ X2) = (X2 ◇ (X3 ◇ (X2 ◇ X2))) := by
    intro X2 X3
    conv => enter [1]; rw [l6 X2 X2 X2 X2]
    conv => enter [1]; rw [l12 X2 X2 X2 X3]
    conv => enter [1, 2, 2]; rw [← l6 X2 X2 X2 X2]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l14 X1 X1]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41660 X1 X2 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1, 2]; rw [l16 (X1 ◇ (X2 ◇ X2)) X0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l16 (sK1 ◇ sK1) X0]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l16 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l19 sK1 sK1]
  have l22 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l17 X1 X2 X1]
    conv => enter [1, 2]; rw [l20 X1 sK1]
  have l23 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l22 sK1 X2 sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l21 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]
  conv => enter [1]; rw [l24 y]

@[equational_result]
theorem Equation316_implies_Equation41665 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41665 G := by
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
  have l3 : ∀ X0 sK2 sK0 : G, (X0 ◇ X0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h316 X0 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l5 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l6 : ∀ X0 sK2 sK0 : G, (X0 ◇ X0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l3 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  have l7 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l5 X0 X1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK2]
  have l8 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK2 sK0]
  have l9 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l7 sK2 X1 sK2 sK0]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l8 sK2 sK0]
  have l11 : ∀ sK0 X1 sK2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l9 sK2 X1 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_41665_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41665 : Equation41665 G) : Equation316 G := by
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
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41665 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41665 (sK1 ◇ (sK1 ◇ sK1)) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l11 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41665 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41665 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41665 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41665 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41665 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41665 X0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l9 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1, 2]; rw [l11 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1, 2]; rw [l4 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 X0]
    conv => enter [1, 2]; rw [← l16 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← l17 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1, 2]; rw [← l19 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l26 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 X0]
    conv => enter [1, 2]; rw [← l18 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK1 X0]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1 sK1]
    conv => enter [1]; rw [← l27 sK1 sK1]
  have l29 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l28 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l30 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l28 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l28 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l30 sK1]
  have l33 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [← l25 sK1 sK1]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l32 sK1]
  have l35 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1]
    conv => enter [1]; rw [l33 sK1]
  have l36 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [← l35 sK1]
  have l37 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [← l31 sK1]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41665 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l24 sK0 X0]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l38 X0 X0 sK0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l34 sK1]
  intro x y
  conv => enter [1]; rw [l40 x y]
  conv => enter [1]; rw [l37 y]

@[equational_result]
theorem Equation316_implies_Equation41670 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41670 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l5 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l4 sK0 X1 sK1]
  have l6 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l5 sK1 X1 sK1]
  have l7 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK3]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_41670_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41670 : Equation41670 G) : Equation316 G := by
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
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41670 sK1 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41670 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41670 X1 X2 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41670 (X0 ◇ X0) X1 X1 X0]
  have l11 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41670 (sK1 ◇ sK1) X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l12 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41670 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l13 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41670 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l2 sK1 (X0 ◇ X0)]
  have l14 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41670 sK1 X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l7 sK1 (X0 ◇ X0)]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41670 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1 sK1]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41670 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l17 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l11 sK1 X1 X0]
  have l18 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l20 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1 sK1]
    conv => enter [1]; rw [← l17 sK1 sK1 sK1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X1 X0]
    conv => enter [1]; rw [← h41670 X0 X1 X0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h41670 sK0 sK0 sK0 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l25 sK1]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [l5 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [← l26 sK1]
  have l30 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41670 X1 X2 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [l22 (X1 ◇ (X1 ◇ X1)) X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l22 sK0 X0]
  have l32 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l22 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK0]
    conv => enter [1, 2]; rw [l32 sK0 sK1]
  have l34 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l30 X1 X2 X1]
    conv => enter [1, 2]; rw [l32 X1 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l36 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l34 sK1 X2 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l38 x y]
  conv => enter [1]; rw [l29 y]

@[equational_result]
theorem Equation316_implies_Equation41677 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41677 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h316 sK1 sK1]
    conv => enter [1]; rw [h316 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1, 2]; rw [h316 X0 sK1]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h316 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1, 2]; rw [← h316 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1]; rw [← h316 sK1 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1, 2]; rw [h316 sK1 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK2]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_41677_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41677 : Equation41677 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41677 X0 X0 X0]
    conv => enter [1]; rw [← h41677 X1 X0 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41677 X1 X2 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X2 ◇ X2)) X0]
  have l3 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l3 sK1 X2 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l6 y]

theorem Equation316_4512_implies_Equation41678 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41678 G := by
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
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation4512_41678_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41678 : Equation41678 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l2 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41678 X0 X0 X0]
    conv => enter [1]; rw [← h41678 X1 X0 X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l9 sK1 sK1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l7 X0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 1]; rw [l7 sK1 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 1]; rw [l7 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l20 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1, 1]; rw [l7 sK1 sK0]
  have l21 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41678 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK1 sK0]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l21 X0 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l22 X0 X0 sK1]
    conv => enter [1]; rw [← l20 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l24 X0 X0 sK1]
    conv => enter [1]; rw [← l18 sK1 X0]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l26 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation316_4512_implies_Equation41679 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41679 G := by
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
  have l14 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [l13 sK1 sK2 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41679_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41679 : Equation41679 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41679 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41679 X0 X1 X1 X1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41679 X0 X1 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [l5 (X1 ◇ (X1 ◇ X0)) sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l9 sK1 X1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 X1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation316_4512_implies_Equation41681 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41681 G := by
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
  have l4 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h316 (sK2 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l4 sK2 sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_41681_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41681 : Equation41681 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41681 X0 X0 X0]
    conv => enter [1]; rw [← h41681 X1 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l6 sK1 X1 X2]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l8 sK1 sK1]
  have l11 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41681 X1 X1 X2]
    conv => enter [1]; rw [l5 X1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l11 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 X1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation316_implies_Equation41682 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41682 G := by
  have l0 : ∀ X1 sK2 : G, (X1 ◇ (X1 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK2]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 sK0 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK0 X0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h316 sK0 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 sK0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l2 sK2 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_41682_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41682 : Equation41682 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41682 X0 sK1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41682 X0 X0 X0]
    conv => enter [1]; rw [← h41682 X1 X0 X0]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 sK1]
    conv => enter [1]; rw [l1 sK1 sK1]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l10 X0 sK1]
    conv => enter [1]; rw [← l13 sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l15 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation316_4512_implies_Equation41683 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41683 G := by
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
  have l11 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l10 sK1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l12 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l11 sK1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_41683_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41683 : Equation41683 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41683 X1 X2 X1 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41683 X0 X1 X2 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41683 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41683 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation316_implies_Equation41687 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41687 G := by
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
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK0]
  have l7 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK0 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK3 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_41687_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41687 : Equation41687 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41687 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41687 X0 X1 X1 X1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41687 X0 X1 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [l5 (X1 ◇ (X0 ◇ X0)) sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l9 sK1 X1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 X1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation316_4512_implies_Equation41690 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41690 G := by
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
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK2 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_41690_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41690 : Equation41690 G) : Equation316 G := by
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
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41690 sK1 ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41690 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l5 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41690 (sK1 ◇ sK1) (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41690 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41690 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41690 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41690 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) = (X2 ◇ (X3 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h41690 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X2 ◇ X3)]
  have l11 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 X0]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
    conv => enter [1]; rw [← l9 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l16 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))]
  have l17 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41690 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41690 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l12 sK1]
    conv => enter [1]; rw [← l17 sK1]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1, 2]; rw [← l12 sK1]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l21 sK0]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l20 sK1]
  have l25 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [h41690 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l22 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 (sK1 ◇ (sK1 ◇ sK1)) sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [l27 sK1 sK0]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41690 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l28 sK1 sK0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l31 x y]
  conv => enter [1]; rw [l24 y]

theorem Equation316_4512_implies_Equation41691 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41691 G := by
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
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK2 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_41691_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41691 : Equation41691 G) : Equation316 G := by
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
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l4 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41691 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41691 (sK1 ◇ (sK1 ◇ sK1)) X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41691 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41691 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1, 2]; rw [← l15 sK1 sK1]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1 sK1]
    conv => enter [1]; rw [← l19 sK1 sK1]
  have l21 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [← l8 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l22 sK1]
  have l25 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [← l15 sK1 sK1]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l24 sK1]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l6 sK1]
    conv => enter [1]; rw [l25 sK1]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [← l27 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [← l23 sK1]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41691 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 X0]
  have l31 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK0]
  have l34 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l31 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ X0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l35 X0 X0 sK0]
    conv => enter [1]; rw [← h41691 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l37 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l36 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l37 X0 sK0]
    conv => enter [1]; rw [← l34 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l38 X0 sK0]
    conv => enter [1]; rw [← l33 sK0 (sK0 ◇ sK0)]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l26 sK1]
  intro x y
  conv => enter [1]; rw [l40 x y]
  conv => enter [1]; rw [l29 y]

theorem Equation316_4512_implies_Equation41692 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41692 G := by
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
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK3 (sK1 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

end Semigroup5
