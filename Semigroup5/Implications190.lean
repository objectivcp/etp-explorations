import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4279_4512_implies_Equation54146 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54146 G := by
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
  conv => enter [1]; rw [l7 x y x x y]
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_54146_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54146 : Equation54146 G) : Equation4279 G := by
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
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54146 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l11 : ∀ sK0 X0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (X3 ◇ (X2 ◇ X0))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
    conv => enter [1]; rw [h54146 sK0 X0 X2 X3]
  have l12 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X2) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l8 X1 X0 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l15 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l12 X1 X0 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l20 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← l15 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l22 : ∀ sK0 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l11 sK0 X2 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 X2 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l21 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l18 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [h54146 X0 sK2 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK2 sK0]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l27 X0 sK2 sK0 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK2 sK0]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [← l26 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

theorem Equation4279_4512_implies_Equation54147 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54147 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK3 sK3]
  have l1 : ∀ X0 sK3 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK3 sK1 sK2
    conv => enter [1]; rw [h4279 X0 (sK3 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK3]
  have l2 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [l1 sK3 sK3 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK3 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 sK3 sK1 sK2]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X0]
  have l5 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [l4 sK3 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK2]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← h4279 (sK1 ◇ (sK2 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [← l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l7 X0 X1 sK1 sK2]
  have l9 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l8 X0 X1 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 sK3 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK3
    conv => enter [1, 1]; rw [l3 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l11 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 X0 sK1]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l14 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [← l11 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l15 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l14 sK1 sK2 X4]
    conv => enter [1]; rw [← l9 X2 X3 X4 sK1 sK2]
  have l16 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l15 sK1 sK2 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w z]

theorem Equation4512_54147_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54147 : Equation54147 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54147 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
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
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

theorem Equation4279_4512_implies_Equation54148 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54148 G := by
  have l0 : ∀ X1 X2 sK0 sK3 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro X1 X2 sK0 sK3
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK3]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK3]
  have l2 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK2 sK0 sK3]
  have l3 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l2 sK2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l0 sK0 sK3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0 sK0 sK3]
  have l5 : ∀ sK0 sK3 X1 X2 X0 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK3 X1 X2 X0
    conv => enter [1]; rw [l0 sK0 sK3 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK0 sK3 X1 X2 X0 : G, (sK0 ◇ (sK3 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK3 X1 X2 X0
    conv => enter [1]; rw [l5 sK0 sK3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l4 sK0 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ sK0 sK3 X1 X2 : G, (sK0 ◇ (sK3 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))))) := by
    intro sK0 sK3 X1 X2
    conv => enter [1]; rw [l6 sK0 sK3 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK0 ◇ (sK3 ◇ sK0)) sK3]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK1 sK1 sK2]
  have l10 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l8 sK0 sK3 X1 X2]
    conv => enter [1, 2, 2, 1]; rw [l1 sK0 sK3 sK1 sK2]
  have l11 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l10 sK1 sK2 X1 X2 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK1 sK1 sK1]
  have l12 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l11 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation4512_54148_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54148 : Equation54148 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54148 X0 X1 sK0 sK0]
  have l4 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h54148 X0 X1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l6 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK2 sK1]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK2 sK1]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 sK1]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

theorem Equation4279_4512_implies_Equation54149 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54149 G := by
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
  intro x y z w u
  conv => enter [1]; rw [l7 x y x x u]
  conv => enter [1]; rw [l4 x u z w]

theorem Equation4512_54149_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54149 : Equation54149 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54149 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54149 sK0 sK0 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54149 sK1 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h54149 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 sK0 X0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4279_4512_implies_Equation54152 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54152 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w w]

theorem Equation4512_54152_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54152 : Equation54152 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54152 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
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
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

theorem Equation4279_4512_implies_Equation54153 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54153 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK0]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK2 sK0]
  have l2 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4279 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4279 sK0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK0 X1 X0]
  have l4 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4279 sK0 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l5 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l4 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X1 X2 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X2 sK3
    conv => enter [1]; rw [l5 sK0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK3]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK2 sK1]
  have l9 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 X1 X2 sK3]
    conv => enter [1, 2, 2, 1]; rw [← l0 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l9 sK1 sK2 X1 X2 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK1 sK1 sK1]
  have l11 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation4512_54153_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54153 : Equation54153 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54153 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l0 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

theorem Equation4279_4512_implies_Equation54157 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54157 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ (X2 ◇ X1)) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 X2 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [l0 sK2 sK3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]

theorem Equation4512_54157_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54157 : Equation54157 G) : Equation4279 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X3 X1 X2 X0 : G, (sK0 ◇ (X3 ◇ (sK0 ◇ sK0))) = ((X1 ◇ X2) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X3 X1 X2 X0
    conv => enter [1]; rw [← h54157 (X1 ◇ X2) X2 sK0 X3 sK0]
    conv => enter [1, 2]; rw [h54157 X2 X1 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54157 sK0 (sK0 ◇ sK0) sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h54157 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 sK0]
  have l4 : ∀ X3 X4 X5 sK0 X0 : G, (X3 ◇ (X4 ◇ (X5 ◇ X3))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X3 X4 X5 sK0 X0
    conv => enter [1]; rw [← h54157 X3 X3 X3 X4 X5]
    conv => enter [1]; rw [h54157 X3 X3 sK0 X0 sK0]
  have l5 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54157 X1 X2 X3 X3 X1]
    conv => enter [1, 2]; rw [h54157 X3 X1 sK0 X0 sK0]
  have l6 : ∀ X3 X4 X5 X1 X2 sK0 X0 : G, (X3 ◇ (X4 ◇ (X5 ◇ X3))) = ((X1 ◇ X2) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X3 X4 X5 X1 X2 sK0 X0
    conv => enter [1]; rw [← h54157 (X1 ◇ X2) X2 X3 X4 X5]
    conv => enter [1, 2]; rw [h54157 X2 X1 sK0 X0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54157 sK0 sK0 sK0 X0 sK0]
  have l8 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ sK2) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [h54157 sK2 sK1 sK0 X0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ X3 X4 X5 X1 X2 sK0 X0 : G, (X3 ◇ (X4 ◇ (X5 ◇ X3))) = (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X3 X4 X5 X1 X2 sK0 X0
    conv => enter [1]; rw [l6 X3 X4 X5 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ X1 X2 X3 sK2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro X1 X2 X3 sK2 sK1
    conv => enter [1]; rw [l5 X1 X2 X3 X1 X1]
    conv => enter [1, 2]; rw [← l8 sK2 sK1 X1 X1]
  have l12 : ∀ X3 X4 X5 sK2 sK1 : G, (X3 ◇ (X4 ◇ (X5 ◇ X3))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro X3 X4 X5 sK2 sK1
    conv => enter [1]; rw [l4 X3 X4 X5 X3 X3]
    conv => enter [1]; rw [← l8 sK2 sK1 X3 X3]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l8 sK2 sK1 sK0 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54157 sK1 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54157 (sK0 ◇ sK0) sK0 sK0 sK0 sK0]
  have l16 : ∀ sK0 X3 X1 X2 X0 : G, (sK0 ◇ (X3 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X3 X1 X2 X0
    conv => enter [1]; rw [l1 sK0 X3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ X3 X4 X5 X1 X2 sK2 sK1 : G, (X3 ◇ (X4 ◇ (X5 ◇ X3))) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ sK2))) := by
    intro X3 X4 X5 X1 X2 sK2 sK1
    conv => enter [1]; rw [l10 X3 X4 X5 X1 X2 X3 X3]
    conv => enter [1, 2, 2]; rw [← l8 sK2 sK1 X3 X3]
  have l18 : ∀ sK0 X3 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X3 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 X3 sK2 sK1
    conv => enter [1]; rw [← h54157 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X3 sK2 sK1]
  have l19 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 sK2 sK1]
  have l20 : ∀ sK0 X3 X1 X2 sK2 sK1 : G, (sK0 ◇ (X3 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ sK2))) := by
    intro sK0 X3 X1 X2 sK2 sK1
    conv => enter [1]; rw [l16 sK0 X3 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK2 sK1 sK0 sK0]
  have l21 : ∀ sK2 sK1 X1 X2 : G, ((sK2 ◇ sK1) ◇ sK2) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ sK2))) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [← l12 sK2 sK2 sK2 sK2 sK1]
    conv => enter [1]; rw [l17 sK2 sK2 sK2 X1 X2 sK2 sK1]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
  have l23 : ∀ sK0 X3 X1 : G, (sK0 ◇ (X3 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X3 X1
    conv => enter [1]; rw [l20 sK0 X3 X1 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK0 sK0 sK0]
  have l24 : ∀ sK2 sK1 X1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 X1 sK0
    conv => enter [1]; rw [l21 sK2 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← l18 sK0 sK2 sK2 sK1]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [l22 sK1 sK2 sK1]
  have l26 : ∀ sK0 X3 X1 sK1 sK2 : G, (sK0 ◇ (X3 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X3 X1 sK1 sK2
    conv => enter [1]; rw [l23 sK0 X3 X1]
    conv => enter [1, 2]; rw [← l14 sK1 sK2 sK0]
  have l27 : ∀ sK2 sK1 X1 : G, ((sK2 ◇ sK1) ◇ sK2) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [l24 sK2 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← l14 sK1 sK2 sK2]
  have l28 : ∀ sK0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 X1 sK1 sK2]
  have l29 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [l27 sK2 sK1 X1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

theorem Equation4279_4512_implies_Equation54158 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54158 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4279 sK2 sK2 sK3]
    conv => enter [1]; rw [h4279 sK2 sK1 sK0]
  have l1 : ∀ X0 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h4279 X0 (sK2 ◇ (sK3 ◇ sK2)) sK4]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK3 sK1 sK0]
  have l2 : ∀ sK3 sK2 sK4 sK1 sK0 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4279 sK3 (sK3 ◇ sK2) sK2]
    conv => enter [1]; rw [l1 sK3 sK2 sK3 sK4 sK1 sK0]
  have l3 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ (X2 ◇ X1)) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK2 sK3]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l3 X1 X0 sK2 sK3]
  have l5 : ∀ sK2 sK3 X1 X2 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 X1 X2 X0
    conv => enter [1]; rw [l3 sK2 sK3 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK2 sK3 X1 X2 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 sK3 X1 X2 X0
    conv => enter [1]; rw [l5 sK2 sK3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK3 ◇ sK2))]
  have l8 : ∀ sK2 sK3 X1 X2 sK1 sK0 sK4 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK3 X1 X2 sK1 sK0 sK4
    conv => enter [1]; rw [l6 sK2 sK3 X1 X2 sK2]
    conv => enter [1, 2, 2]; rw [h4279 sK2 (sK1 ◇ (sK0 ◇ sK1)) sK4]
  have l9 : ∀ sK2 sK3 X1 X2 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X1 ◇ (X2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK3 X1 X2 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 X1 X2 sK1 sK0 sK4]
    conv => enter [1, 2, 2, 1]; rw [l0 sK1 sK0 sK2 sK3]
  have l10 : ∀ sK2 sK3 X1 X2 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X1 ◇ (X2 ◇ ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))))) := by
    intro sK2 sK3 X1 X2
    conv => enter [1]; rw [l9 sK2 sK3 X1 X2 sK2 sK2 sK2]
    conv => enter [1, 2, 2]; rw [← l2 sK3 sK2 sK2 sK2 sK2]
  have l11 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l10 sK2 sK3 X1 sK2]
    conv => enter [1, 2]; rw [← l7 sK2 sK3 sK2 (sK3 ◇ sK2)]
  have l12 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK3 sK4]
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

theorem Equation4512_54158_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54158 : Equation54158 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54158 sK0 sK0 X0 sK1 sK2]
  have l1 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54158 sK1 sK2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4279_4512_implies_Equation54061 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54061 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4279 sK0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4279 sK0 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [l4 sK0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK0 ◇ sK1) sK1]
  have l7 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [l6 sK0 X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [l8 y y]

theorem Equation4512_54061_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54061 : Equation54061 G) : Equation4279 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54061 X0 X1]
    conv => enter [1]; rw [← h54061 X2 X1]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54061 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54061 X0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54061 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54061 (sK0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l15 sK0 X0]
  have l26 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l15 sK0 X0]
  have l27 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l26 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l25 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l29 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l22 sK0 X1]
    conv => enter [1]; rw [← l27 X0 sK0 X1]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l28 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l17 sK0]
  have l31 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l29 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l32 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l9 X2 X1 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54061 X0 X1]
  have l33 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X2))) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← h54061 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [l9 X2 X1 X0]
  have l34 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l33 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X0))]
  have l35 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l32 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l36 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← l34 X2 X1 X0]
    conv => enter [1]; rw [l30 X2 sK0]
  have l37 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l35 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X0))]
  have l38 : ∀ X2 X1 sK0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l37 X2 X1 X2]
    conv => enter [1, 2]; rw [l36 X1 X1 X2 sK0]
  have l39 : ∀ sK0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l38 X2 X1 sK0]
  have l40 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l39 sK0 X2 X1]
  have l41 : ∀ sK0 X2 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l40 sK0 X2 X1]
  have l42 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l15 sK0 sK2]
  have l43 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l9 X0 sK2 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = (X0 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l43 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [← l45 sK0 sK1 sK2]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l47 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l51 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l9 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l50 sK1 sK2 sK0]
  have l52 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l52 sK0 sK1 sK2 sK0]
  have l54 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l53 sK0 sK1 sK2]
  have l55 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [← l54 X0 sK0 sK1 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l56 x y z]

theorem Equation4279_4512_implies_Equation54128 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54128 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK0]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4279 sK0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK0 X1 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK2 sK1]
  have l5 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l1 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l6 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK2 ◇ sK1) sK1]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l7 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54128_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54128 : Equation54128 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54128 X0 X1 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
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
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4279_4512_implies_Equation54062 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54062 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h4279 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
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
  intro x y z
  conv => enter [1]; rw [← h4279 x x y]
  conv => enter [1]; rw [l0 x z x z]
  conv => enter [1]; rw [← l4 y z z x]

theorem Equation4512_54062_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54062 : Equation54062 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54062 X0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54062 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l3 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))]
    conv => enter [1]; rw [← h54062 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1, 2]; rw [← l8 sK0 X1]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54062 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 X0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l11 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 X0]
  have l13 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l12 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4279_4512_implies_Equation54127 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54127 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h4279 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
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
  intro x y z
  conv => enter [1]; rw [← h4279 x x y]
  conv => enter [1]; rw [l0 x y x y]
  conv => enter [1]; rw [← l4 z y y x]

theorem Equation4512_54127_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54127 : Equation54127 G) : Equation4279 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54127 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X3 ◇ ((X2 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h54127 X0 X1 X2]
    conv => enter [1]; rw [← h54127 X3 (X2 ◇ X1) X2]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54127 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X3 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l8 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X3]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l13 : ∀ X3 X2 X1 sK0 : G, (X3 ◇ (X2 ◇ (X1 ◇ X3))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X3 X2 X1 sK0
    conv => enter [1]; rw [← l11 X2 X3 X1 X3]
    conv => enter [1, 2]; rw [l10 X3 X1 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l18 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← h54127 (X0 ◇ X2) X2 X1]
    conv => enter [1, 2]; rw [l10 X2 X0 sK0]
  have l19 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X2) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l10 X1 X0 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l22 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l19 X1 X0 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X2]
  have l23 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l18 X1 X2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X2 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l24 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l28 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2 sK0
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l22 X1 X0 X2 sK0]
  have l29 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l23 X1 X2 X1 sK0]
    conv => enter [1]; rw [l13 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l31 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l29 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l25 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l30 sK0]
  have l33 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l31 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l34 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l33 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l27 sK0]
  have l35 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l28 X1 X1 X2 sK0]
    conv => enter [1]; rw [l34 X1 X2 sK0]
  have l36 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l37 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
  have l38 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l37 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l35 sK0 sK2 X0]
  have l39 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l36 sK2 sK1 sK0]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l39 sK0 sK2 sK1]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
  have l42 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l10 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
    conv => enter [1, 2]; rw [← l41 sK0 sK2 sK1]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l38 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l42 sK0 sK2 sK0]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l43 sK0 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [← l44 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l45 x y z]

theorem Equation4279_4512_implies_Equation54129 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54129 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h4279 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
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
  intro x y z w
  conv => enter [1]; rw [← h4279 x x y]
  conv => enter [1]; rw [l0 x w x w]
  conv => enter [1]; rw [← l4 z w w x]

theorem Equation4512_54129_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54129 : Equation54129 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54129 X0 X1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4279_4512_implies_Equation54120 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54120 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l1 X1 X0 sK1 sK2]
  have l3 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l1 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l4 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK2 ◇ sK1) sK1]
  have l7 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l6 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK1 (sK2 ◇ sK1)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_54120_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54120 : Equation54120 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54120 (sK0 ◇ sK0) X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54120 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54120 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54120 X0 X1 sK0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l10 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54120 sK0 X0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l20 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54120 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l25 sK0]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

theorem Equation4279_4512_implies_Equation54064 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54064 G := by
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
  intro x y z
  conv => enter [1]; rw [← l0 y z x]
  conv => enter [1]; rw [l8 y z y]

theorem Equation4512_54064_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54064 : Equation54064 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54064 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54064 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54064 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (X1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54064 X0 sK0 X1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h54064 sK0 sK1 sK2]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l11 sK0 X0]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l23 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l18 X0 sK0 X1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l25 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((X1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X1 ◇ sK0) (X0 ◇ (sK0 ◇ X0))]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l23 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l29 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l25 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l32 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l29 sK0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 sK0]
  have l33 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l32 sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l33 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l13 sK0]
  have l35 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l34 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l11 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l35 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l22 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l22 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l38 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54064 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1, 2, 2]; rw [← l31 sK0 sK1 sK2]
  have l41 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l42 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l43 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK1)) (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l44 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l37 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l45 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l43 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l46 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l45 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK1 sK2]
  have l47 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l46 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l48 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l47 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
    conv => enter [1]; rw [← l48 X0 sK0 sK1 sK2]
  have l50 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l51 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l50 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 X0 sK0 sK0]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l51 sK0 X0]
  have l53 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l52 sK0 X0]
  have l54 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l53 sK0 X0]
  have l55 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l36 sK0 X0]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l55 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l56 sK0 X0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l58 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l57 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0 (sK0 ◇ sK0)]
  have l59 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l58 sK0 X0]
    conv => enter [1, 2]; rw [← l22 sK0]
  have l60 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l54 sK0 X0]
    conv => enter [1]; rw [← h54064 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l61 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l59 sK0 X0]
    conv => enter [1]; rw [l60 X0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l61 x y z]

theorem Equation4279_4512_implies_Equation54124 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54124 G := by
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
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l9 z y z]

theorem Equation4512_54124_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54124 : Equation54124 G) : Equation4279 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54124 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h54124 (sK2 ◇ sK2) sK2 sK1]
    conv => enter [1, 2]; rw [h54124 sK2 sK2 sK1]
  have l3 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [h54124 X0 sK2 sK1]
  have l4 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h54124 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← h54124 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1]
    conv => enter [1]; rw [← l0 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l7 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK2 sK1]
  have l8 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l3 X0 sK2 X1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l10 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0]
  have l11 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) = (X0 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l8 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l13 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l10 sK2 sK1 sK0]
  have l14 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK2 sK1]
  have l15 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l7 sK2 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 sK0]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54124 sK1 sK2 sK1]
    conv => enter [1]; rw [l14 sK1 sK2]
  have l17 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l7 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l17 sK2 sK1 X0]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h54124 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) sK2 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK2]
  have l20 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54124 X0 sK2 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK2]
  have l21 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l20 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l22 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l19 sK1 sK2]
  have l23 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l21 X0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54124 sK1 sK2 sK1]
    conv => enter [1]; rw [← l22 sK2 sK1]
  have l25 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l23 X0 sK2 sK1]
    conv => enter [1, 2, 2, 2]; rw [l7 sK2 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK2 sK1]
  have l27 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l25 X0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [l1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0]
  have l29 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l27 X0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← l15 sK2 sK1 X0]
  have l30 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l29 X0 sK2 sK1]
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0]
  have l31 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK1]
    conv => enter [1]; rw [← l30 X0 sK2 sK1 sK1]
  have l32 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = ((sK2 ◇ X0) ◇ ((sK2 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h54124 X1 X0 (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l31 X0 sK2 sK1]
  have l33 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ ((sK2 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l32 X1 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 X0 ((sK2 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l34 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l33 X1 X0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l35 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l34 X1 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l36 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l35 X1 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l37 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l18 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l36 X1 X0 sK2 sK1]
  have l38 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [← l37 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [l7 sK2 sK1]
  have l39 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [l38 X1 X0 sK2 sK1]
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0]
  have l40 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK1]
    conv => enter [1]; rw [← l39 X1 X0 sK1 sK2 sK1]
  have l41 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l41 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l42 x y z]

theorem Equation4279_4512_implies_Equation54132 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54132 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK3 sK0]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l1 X1 X0 sK1 sK2]
  have l3 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l1 sK1 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK1 sK2 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l4 sK1 sK2 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4279 sK1 (sK0 ◇ sK3) sK3]
  have l7 : ∀ sK1 sK2 X1 X2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X1 X2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 X1 X2 sK0 sK3]
    conv => enter [1, 2, 2, 2]; rw [l0 sK3 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l7 sK1 sK2 X1 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK1 (sK1 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]
  conv => enter [1]; rw [l8 z w z]

theorem Equation4512_54132_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54132 : Equation54132 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54132 X0 X1 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54132 sK0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54132 sK0 sK0 sK1 sK2]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54132 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation4280_implies_Equation4346 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4346 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y y z]

@[equational_result]
theorem Equation4346_implies_Equation4280 (G : Type*) [Magma G] (h4346 : Equation4346 G) : Equation4280 G := by
  have l0 : ∀ X1 sK0 sK2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [← h4346 X1 X1 sK0]
    conv => enter [1]; rw [h4346 X1 X1 sK2]
  have l1 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4346 X0 sK2 X0]
    conv => enter [1]; rw [← h4346 X1 sK2 X0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation4280_implies_Equation4355 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4355 G := by
  have l0 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation4355_implies_Equation4280 (G : Type*) [Magma G] (h4355 : Equation4355 G) : Equation4280 G := by
  intro x y z
  conv => enter [1]; rw [h4355 x x y z]

theorem Equation4280_4512_implies_Equation54200 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54200 G := by
  have l0 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 X1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4280 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK0]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4280 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK0 sK1]
  have l6 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 (sK1 ◇ sK1) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 X1 X0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4280 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 X0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK0 X0]
  have l11 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l10 sK0 sK1 X4]
    conv => enter [1]; rw [← l5 X2 X3 X4 sK0 sK1]
  have l12 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l11 sK0 sK1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z
  conv => enter [1]; rw [l12 x y y x z]

theorem Equation4512_54200_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54200 : Equation54200 G) : Equation4280 G := by
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
    conv => enter [1]; rw [h54200 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [h54200 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54200 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54206 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54206 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4280 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [h4280 sK1 sK0 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_54206_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54206 : Equation54206 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54206 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h54206 (sK0 ◇ sK0) X0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54206 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54218 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54218 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK2 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK2]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK2]
  have l3 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z x]
  conv => enter [1]; rw [l2 z x y]

theorem Equation4512_54218_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54218 : Equation54218 G) : Equation4280 G := by
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
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X2 ◇ (X3 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [← h54218 X2 X3 (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54218 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54218 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54218 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54218 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54218 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54218 X0 sK0 X1]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54218 X0 sK0 X1]
  have l13 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54218 X0 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ X0)]
  have l14 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54218 X0 (sK2 ◇ sK2) X1]
  have l15 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ X0))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l14 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h54218 (sK2 ◇ sK2) sK1 X0]
  have l16 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54218 sK0 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54218 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l11 sK0 X1 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l2 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l21 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l15 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← h54218 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 sK0 X0]
    conv => enter [1]; rw [← h54218 X0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l26 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [l21 sK2 sK1 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l24 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 X0]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l25 X0 sK0]
    conv => enter [1]; rw [l28 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1, 2]; rw [← l31 sK0 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l33 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← l31 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0 sK0]
    conv => enter [1]; rw [l35 sK0]
  have l37 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l26 sK1 sK2 (sK0 ◇ sK0)]
  have l39 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 (sK1 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
  have l40 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l37 sK1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK2 sK1]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l39 sK1 sK2 sK0]
  have l42 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2]
  have l43 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK0]
    conv => enter [1]; rw [← l31 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [← l43 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation4280_4512_implies_Equation54226 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54226 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4280 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK0]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4280 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK0 sK1]
  have l6 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 (sK1 ◇ sK1) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 X1 X0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4280 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 X0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK0 X0]
  have l11 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l10 sK0 sK1 X4]
    conv => enter [1]; rw [← l5 X2 X3 X4 sK0 sK1]
  have l12 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l11 sK0 sK1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z
  conv => enter [1]; rw [l12 x y y z x]

theorem Equation4512_54226_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54226 : Equation54226 G) : Equation4280 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54226 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54226 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h54226 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h54226 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54226 sK0 X0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l8 X0 sK0 X1]
    conv => enter [1]; rw [← h54226 X1 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l9 sK0 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54226 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1]; rw [l9 X1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l14 sK0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54226 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l13 sK0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l21 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l23 X0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [h54226 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l27 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (((sK0 ◇ sK0) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l26 sK0 X0 X1]
  have l28 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l27 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l29 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l28 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l30 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l29 X0 sK0 X1]
    conv => enter [1]; rw [← h54226 X1 (sK0 ◇ sK0) X0]
  have l31 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l30 X0 sK0 X1]
    conv => enter [1]; rw [l21 X1 (sK0 ◇ sK0) sK0]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X1]
    conv => enter [1]; rw [← l31 X0 sK0 X1]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1]
    conv => enter [1, 2]; rw [l9 sK0 sK0 X1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK0 ◇ sK0)]
  have l35 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l33 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l35 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ (sK2 ◇ sK2))]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l36 sK1 sK0 sK2 X0]
  have l39 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l39 sK0 X0 sK0 sK0]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54226 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l40 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l42 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l41 X0 X1 sK0]
    conv => enter [1]; rw [← l25 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l42 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54228 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54228 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4280 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4280 sK2 (sK2 ◇ sK2) sK2]
  intro x y z
  conv => enter [1]; rw [← h4280 z x y]
  conv => enter [1]; rw [l0 z y]

theorem Equation4512_54228_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54228 : Equation54228 G) : Equation4280 G := by
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
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54228 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54228 X0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54228 X0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54228 X0 sK2 sK2]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ sK2 X2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X2 X1 X0
    conv => enter [1]; rw [← h54228 X1 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [l11 sK2 X0]
  have l18 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l11 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l19 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l11 sK2 sK1]
    conv => enter [1]; rw [l18 sK2 X0 X1]
  have l20 : ∀ X1 X0 sK2 X2 sK0 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK2 X2 sK0
    conv => enter [1]; rw [← l17 sK2 X2 X1 X0]
    conv => enter [1, 2]; rw [l12 X2 X2 sK0]
  have l21 : ∀ sK1 sK2 X2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 X2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l20 sK1 sK1 sK2 X2 sK0]
  have l22 : ∀ sK2 X1 X0 sK1 : G, ((sK2 ◇ sK2) ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [← h54228 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l11 sK2 sK1]
  have l23 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [← l22 sK2 X1 X0 sK1]
    conv => enter [1, 2]; rw [l12 X1 X1 sK0]
  have l24 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l21 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l23 X0 sK1 sK2 sK1 sK1]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 (sK2 ◇ sK2)]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1]; rw [h54228 sK1 (sK0 ◇ sK0) sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [← l27 sK1 sK2 sK0]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ (sK2 ◇ sK2))]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [← l25 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l24 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l33 x x y z]

theorem Equation4280_4512_implies_Equation54229 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54229 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [h4280 sK2 X0 sK2]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h4280 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK2) sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 X0 sK1]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← h4280 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l3 X0 X1 sK1 sK2]
  have l5 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK1 sK2]
  have l6 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 (sK2 ◇ sK2) X1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 X1 X0]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4280 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X0 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [l9 sK2 sK1 X0]
  have l11 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l10 sK1 sK2 X4]
    conv => enter [1]; rw [← l5 X2 X3 X4 sK1 sK2]
  have l12 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l11 sK1 sK2 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l12 x y y z w]

theorem Equation4512_54229_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54229 : Equation54229 G) : Equation4280 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l2 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54229 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ X1)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l8 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
  have l10 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [← h54229 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1]
  have l11 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← h54229 (X1 ◇ X2) X0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54229 sK0 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [h54229 (sK0 ◇ sK0) X0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h54229 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54229 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l13 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h54229 X0 X0 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l20 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54229 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54233 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54233 G := by
  have l0 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK3 sK3 sK0]
    conv => enter [1]; rw [h4280 sK3 X0 sK0]
  have l1 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1]; rw [h4280 sK2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK3]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK3 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 X0 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [h4280 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l2 z w y]

theorem Equation4512_54233_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54233 : Equation54233 G) : Equation4280 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X1 ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54233 X0 sK2 sK2 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 (X0 ◇ X1) sK2 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l1 X0 X1 sK2 sK1]
  have l3 : ∀ X2 sK0 X0 sK2 : G, (X2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 sK0 X0 sK2
    conv => enter [1]; rw [h54233 X2 sK0 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [← l0 X0 sK2 X2]
  have l4 : ∀ sK1 sK2 X2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l3 X2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]

@[equational_result]
theorem Equation4280_implies_Equation54235 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54235 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4280 sK0 (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← h4280 x x y]
  conv => enter [1]; rw [l0 x z]

theorem Equation4512_54235_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54235 : Equation54235 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54235 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h54235 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h54235 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 X1 sK0]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X1]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [← l4 sK2 (sK0 ◇ sK0)]
  have l11 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h54235 X0 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [h54235 sK2 (X0 ◇ (X0 ◇ X0)) X2]
  have l12 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l4 sK2 sK2]
    conv => enter [1]; rw [← l11 sK2 X0 X1 sK2]
  have l13 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [l12 sK2 X0 X1]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54235 X0 X1 X0]
    conv => enter [1]; rw [← l13 sK0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

theorem Equation4280_4512_implies_Equation54237 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54237 G := by
  have l0 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← h4280 sK1 X1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK1]
  have l1 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4280 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 X0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X1 sK0]
  have l4 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← h4280 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK0]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l5 X0 X1 sK0 sK1]
  have l7 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l6 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 (sK1 ◇ sK1) X1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X1 X0]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4280 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 X0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l11 sK0 sK1 X4]
    conv => enter [1]; rw [← l6 X2 X3 X4 sK0 sK1]
  have l13 : ∀ sK0 sK1 X2 X3 X4 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK0 sK1 X2 X3 X4
    conv => enter [1]; rw [l12 sK0 sK1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z
  conv => enter [1]; rw [l13 x y z x z]

theorem Equation4512_54237_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54237 : Equation54237 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54237 (sK0 ◇ sK0) X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (X0 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h54237 X0 X1 (sK2 ◇ sK2)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 X0]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54237 sK2 X0 sK2]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54237 sK0 X0 (sK0 ◇ sK0)]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l7 sK2 X0]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK2 X0]
  have l11 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 X0]
  have l12 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l7 sK2 sK0]
  have l13 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l7 sK2 sK0]
  have l14 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l13 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ sK0)]
  have l15 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l12 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 sK0]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l18 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l19 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l18 sK2 X0]
    conv => enter [1]; rw [l15 sK2 X0 sK0]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l17 sK1 sK2]
  have l21 : ∀ sK2 X0 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l19 sK2 X0 sK0]
  have l22 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h54237 (sK2 ◇ sK2) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l14 sK2 sK0]
  have l23 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l22 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l2 sK2 (sK0 ◇ sK0)]
  have l24 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l23 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l21 sK2 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l24 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l7 sK2 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l25 sK2 X0 sK0]
  have l27 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l11 sK2 sK2]
    conv => enter [1]; rw [← l26 sK0 sK2 sK2]
  have l28 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l27 sK2 sK0]
    conv => enter [1]; rw [l16 sK2 sK0]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54237 sK0 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l31 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l32 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l28 sK0 sK2]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK2]
  have l35 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l33 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l28 sK0 sK2]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l35 sK0 X0 X1 sK0]
  have l37 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK0 X1]
  have l38 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l28 sK0 sK2]
    conv => enter [1]; rw [l37 sK0 X1]
  have l39 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l38 sK0 sK0 X1]
  have l40 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l7 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l8 sK0 sK0]
  have l41 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK0]
    conv => enter [1]; rw [l40 sK2 sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0 sK2]
    conv => enter [1]; rw [l41 sK2 sK0]
  have l43 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l2 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l34 sK0 sK2]
  have l44 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l34 sK0 sK2]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l44 sK2 sK0]
  have l46 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l21 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l43 sK2 sK0]
  have l47 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l7 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l46 sK2 sK0]
  have l48 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [l47 sK2 sK0]
  have l49 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l16 sK2 sK0]
    conv => enter [1]; rw [l48 sK2 sK0]
  have l50 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0 sK2]
    conv => enter [1]; rw [l49 sK2 sK0]
  have l51 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h54237 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l8 sK0 sK0]
  have l52 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54237 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h54237 sK1 sK1 (sK2 ◇ sK2)]
  have l53 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h54237 sK1 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [h54237 sK1 X1 (sK2 ◇ sK2)]
  have l54 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l53 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X1 X1 (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l55 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l52 sK1 X0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l56 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54237 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l51 sK2 sK1 sK0]
  have l57 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l54 sK1 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l58 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h54237 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l55 sK1 sK2 sK2]
  have l59 : ∀ sK2 sK1 X1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [← h54237 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l57 sK1 sK2 X1 sK2]
  have l60 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l51 sK2 sK1 sK0]
    conv => enter [1]; rw [l58 sK2 sK1]
  have l61 : ∀ sK1 sK0 X1 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 sK0 X1 sK2
    conv => enter [1]; rw [← l51 sK2 sK1 sK0]
    conv => enter [1]; rw [l59 sK2 sK1 X1]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2 sK1]
    conv => enter [1]; rw [l60 sK1 sK1 sK2]
  have l63 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l56 sK1 sK2 sK1]
    conv => enter [1]; rw [l61 sK1 sK1 X1 sK2]
  have l64 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l63 sK1 sK2 X1]
    conv => enter [1, 2, 2]; rw [← l62 sK1 sK2]
  have l65 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l45 sK0 sK2]
  have l66 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [← l65 sK1 sK2 sK0]
  have l67 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l50 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l68 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [l67 sK1 sK0 sK2]
  have l69 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h54237 (sK1 ◇ (sK2 ◇ sK2)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l66 sK1 sK2 sK0]
  have l70 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l69 sK1 sK2 X0 sK0]
  have l71 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l28 sK0 sK2]
    conv => enter [1]; rw [l70 sK0 sK1 sK2 X0]
  have l72 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK2]
    conv => enter [1]; rw [l71 sK2 sK0 sK1 X0]
  have l73 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK2]
  have l74 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l7 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l8 sK0 sK2]
  have l75 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK2]
    conv => enter [1]; rw [l74 sK2 sK0]
  have l76 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l75 sK2 sK0]
    conv => enter [1, 2]; rw [← l73 sK0 sK2]
  have l77 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l76 sK2 sK0]
  have l78 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l77 sK2 sK0]
  have l79 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2 sK1]
    conv => enter [1]; rw [← l78 sK1 sK2 sK1]
  have l80 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l68 sK1 sK2 sK0]
  have l81 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l82 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54237 (sK1 ◇ (sK2 ◇ sK2)) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l62 sK1 sK2]
  have l83 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l82 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l84 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l83 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l85 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l84 sK1 sK2 X0]
    conv => enter [1]; rw [← l81 sK0 ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) sK1 sK2]
  have l86 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l85 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l20 sK1 sK2]
  have l87 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l86 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l79 sK1 sK2]
  have l88 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l87 sK1 sK2 sK0 sK0]
  have l89 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l88 sK0 sK1 sK2]
  have l90 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1]; rw [← l89 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l90 x y z]

theorem Equation4280_4512_implies_Equation54238 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54238 G := by
  have l0 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← h4280 sK2 X1 sK2]
    conv => enter [1]; rw [h4280 sK2 X0 sK2]
  have l1 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h4280 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK2) sK2 X0]
  have l2 : ∀ sK2 X1 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [l1 sK2 X1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 X1 sK1]
  have l4 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [← h4280 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK2) sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l4 X0 X1 sK2 sK1]
  have l6 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l5 X0 X1 sK1 sK2]
  have l7 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l6 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 (sK2 ◇ sK2) X1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1 X0]
    conv => enter [1]; rw [← l8 sK1 sK2 X1 X0]
  have l10 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4280 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 X0 sK2]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 sK1 X0]
  have l12 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l11 sK1 sK2 X4]
    conv => enter [1]; rw [← l6 X2 X3 X4 sK1 sK2]
  have l13 : ∀ sK1 sK2 X2 X3 X4 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l12 sK1 sK2 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l13 x y z x w]

theorem Equation4512_54238_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54238 : Equation54238 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54238 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54238 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54250 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54250 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y w]
  conv => enter [1]; rw [l2 x w z]

theorem Equation4512_54250_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54250 : Equation54250 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54250 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54250 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l5 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54252 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54252 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y y]
  conv => enter [1]; rw [l2 y x z]

theorem Equation4512_54252_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54252 : Equation54252 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54252 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54252 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54252 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54252 X0 (X0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 X0 X0 X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54252 X0 X1 (X1 ◇ (X0 ◇ X0))]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ X1))]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l10 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

end Semigroup5
