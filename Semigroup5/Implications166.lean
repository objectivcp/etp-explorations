import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation41_implies_Equation42136 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42136 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42136_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42136 : Equation42136 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42136 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h42136 X0 sK0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42136 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42136 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42136 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X1 ◇ (sK0 ◇ X0)))]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l4 ((sK0 ◇ sK0) ◇ X0) sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42136 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h42136 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X0 ◇ X1) ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42136 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l7 sK0 (X0 ◇ X1)]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← l9 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [← l14 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l22 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 X0 X1]
    conv => enter [1]; rw [← l21 X0 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l20 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42136 X0 X1 sK0]
    conv => enter [1]; rw [l26 sK0 (X1 ◇ (X1 ◇ (sK0 ◇ X0)))]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [l24 sK0 X1 (X1 ◇ (sK0 ◇ X0))]
  have l29 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [h42136 X2 X0 X1]
    conv => enter [1, 2]; rw [l28 X0 (X0 ◇ (X1 ◇ X2)) sK0]
  have l30 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l28 (X1 ◇ X2) X0 sK0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ sK0) sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ X2 X0 sK0 : G, (X2 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [l29 X2 X0 X2 sK0]
    conv => enter [1]; rw [l30 X2 (X0 ◇ (X2 ◇ X2)) (sK0 ◇ sK0) sK0]
  have l34 : ∀ X2 X0 sK0 : G, (X2 ◇ X0) = (sK0 ◇ sK0) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [l33 X2 X0 sK0]
    conv => enter [1]; rw [← l32 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l34 y z x]

@[equational_result]
theorem Equation41_implies_Equation42138 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42138 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z y]

theorem Equation4512_42138_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42138 : Equation42138 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42138 X0 X1 X0]
    conv => enter [1]; rw [← h42138 X2 X1 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42138 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42139 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42139 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42139_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42139 : Equation42139 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42139 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42139 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42139 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l4 sK0 X1 X2]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (X1 ◇ X2)) X1]
  have l6 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l5 sK0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ X2)]
  have l7 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l6 sK0 X1 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X1 ◇ X2)]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42139 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l7 sK0 X1 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42140 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42140 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK1)]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 sK0 sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_42140_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42140 : Equation42140 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42140 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X4 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h42140 (X1 ◇ (X2 ◇ X0)) X3 X4 X1]
    conv => enter [1, 2, 2]; rw [← h42140 X0 X1 X3 X2]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42140 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X1 ◇ (X4 ◇ X0)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42140 X0 X1 X0 X0]
  have l4 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l5 : ∀ X2 X3 X1 : G, (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := by
    intro X2 X3 X1
    conv => enter [1]; rw [l0 X2 X3 X2 X2 X1]
    conv => enter [1]; rw [← h42140 (X1 ◇ X2) X3 X2 X2]
  have l6 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ X0) ◇ X3) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [l4 X4 X3 X0 X1 X2]
    conv => enter [1]; rw [← l3 (X2 ◇ X0) X3 X1]
  have l7 : ∀ X4 X3 X0 X1 : G, (X4 ◇ (X3 ◇ (X0 ◇ X1))) = (X0 ◇ X3) := by
    intro X4 X3 X0 X1
    conv => enter [1]; rw [l6 X4 X3 X0 X1 X4]
    conv => enter [1]; rw [← l5 X0 X3 X4]
  have l8 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ X3) := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1 X3]
    conv => enter [1]; rw [l7 X3 X3 X0 X1]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42142 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42142 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK3)]
  have l3 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l3 sK2 sK0 sK3]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_42142_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42142 : Equation42142 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42142 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42142 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (X2 ◇ X1)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42142 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X1))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l4 sK0 X1 X2]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (X2 ◇ X1)) X1]
  have l7 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X1))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l6 sK0 X2 X1]
    conv => enter [1]; rw [l0 sK0 (X2 ◇ X1)]
  have l8 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l7 sK0 X2 X1]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X2 ◇ X1)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0 sK1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42142 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1 (X1 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation42143 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42143 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK0 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_42143_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42143 : Equation42143 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42143 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42143 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (X2 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42143 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 X2]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (X2 ◇ X2)) sK0]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l0 sK0 (X2 ◇ X2)]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X2 ◇ X2)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 (sK1 ◇ sK2)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42144 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42144 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ sK0)]
  have l3 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK3 sK3]
    conv => enter [1, 2]; rw [l2 sK3 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l3 sK3 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

theorem Equation4512_42144_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42144 : Equation42144 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42144 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42144 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42144 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [l3 sK0 X1 X2 X3]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X2 ◇ X3)]
  have l7 : ∀ sK0 X1 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X3))) := by
    intro sK0 X1 X3
    conv => enter [1]; rw [l6 sK0 X1 sK0 X3]
    conv => enter [1, 2]; rw [l2 sK0 sK0 X3]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42144 X0 X1 X2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 X1 X0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42145 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42145 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK2 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z y]

theorem Equation4512_42145_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42145 : Equation42145 G) : Equation41 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h42145 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42145 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l0 X0 X1 X2 X0]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42145 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42145 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42145 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42145 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h42145 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h42145 sK0 X0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42145 (X0 ◇ (sK0 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h42145 sK0 (X0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l9 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l10 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1 sK0 X0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42145 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h42145 sK0 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42145 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42145 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l14 sK0 (X0 ◇ (X1 ◇ X1))]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42145 sK0 X0 sK0]
    conv => enter [1]; rw [l14 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l3 X0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l17 X1 sK0 X1]
    conv => enter [1]; rw [← h42145 X1 sK0 X1]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l24 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
  have l25 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l6 sK0 sK1 sK2]
  have l26 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l25 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l24 sK1 sK2 sK0]
  have l28 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l26 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l20 (sK1 ◇ sK2) sK0]
  have l30 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK2 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l28 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l12 (sK1 ◇ sK2) sK0 X0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l32 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK2 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l30 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l23 sK2 sK0 (X0 ◇ sK0)]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l20 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l34 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l3 sK2 X0 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1 X0 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l20 sK0 sK0]
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
  have l37 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h42145 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l36 sK0 sK1 sK2]
  have l38 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l37 sK1 sK2 X0 sK0]
  have l39 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1, 2]; rw [l38 sK0 (X0 ◇ (X1 ◇ X1)) sK1 sK2]
    conv => enter [1]; rw [← h42145 X1 (sK1 ◇ sK2) X0]
  have l40 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h42145 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [l38 sK0 (sK0 ◇ sK0) sK1 sK2]
  have l41 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l20 (sK1 ◇ sK2) sK0]
  have l42 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ sK0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [h42145 X1 sK0 X1]
    conv => enter [1]; rw [l39 X1 sK0 X1 sK1 sK2]
  have l43 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ sK2) sK0]
  have l44 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l43 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK1 sK0 sK2]
  have l46 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 sK1 sK0 sK2]
  have l47 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l34 sK2 sK2 sK0 sK1]
    conv => enter [1]; rw [← l46 sK1 sK2 sK0]
  have l48 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l47 sK2 sK1 sK0]
    conv => enter [1]; rw [l19 (sK1 ◇ sK2) sK0]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [← l48 sK2 sK0 sK0]
  have l50 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h42145 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l49 sK2 sK0]
  have l51 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (sK2 ◇ X0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h42145 sK0 X0 sK0]
    conv => enter [1]; rw [← l50 sK2 X0 sK0 sK0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l51 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) sK0]
  have l53 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ sK2) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [l51 sK0 (X0 ◇ (X1 ◇ X1)) sK2]
    conv => enter [1]; rw [← h42145 X1 sK2 X0]
  have l54 : ∀ X1 sK0 sK2 : G, (X1 ◇ sK0) = (X1 ◇ sK2) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [h42145 X1 sK0 X1]
    conv => enter [1]; rw [l53 X1 sK0 X1 sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ sK2)]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1 sK0]
  have l57 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l57 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l58 x y z]

@[equational_result]
theorem Equation41_implies_Equation42148 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42148 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42148_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42148 : Equation42148 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X1 X2 sK2 X0 : G, (sK1 ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 X1 X2 sK2 X0
    conv => enter [1]; rw [h42148 sK1 X1 X2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X2 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h42148 (sK0 ◇ sK0) X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42148 X1 X2 X3 (X3 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h42148 X0 X1 X3 X1]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42148 X0 (sK0 ◇ sK0) sK0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l5 : ∀ X2 X1 X0 X3 X4 : G, (X2 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X2 X1 X0 X3 X4
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X2 ◇ (X0 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h42148 X0 X1 X2 X3]
  have l6 : ∀ X2 X1 X0 X3 X4 : G, (X2 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X2 X1 X0 X3 X4
    conv => enter [1]; rw [l5 X2 X1 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42148 sK0 X1 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X1 sK0 sK0]
  have l9 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l1 sK1 X1 sK1 sK2 sK1]
    conv => enter [1]; rw [← h42148 (sK1 ◇ sK2) X1 sK1 sK1]
  have l10 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l6 X2 X1 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X3)) X4]
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK0 X0]
    conv => enter [1]; rw [← l3 X0 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l12 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l10 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← l3 X4 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l9 sK1 (sK2 ◇ X0) sK2]
  have l14 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [l12 (sK1 ◇ sK2) sK2 X0]
  have l15 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h42148 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l11 X1 sK0 X0]
  have l16 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l11 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l17 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l16 X0 sK0 X0 X2]
    conv => enter [1]; rw [l12 X0 X2 (sK0 ◇ sK0)]
  have l18 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 X1 X2 X1 X0 X1]
    conv => enter [1]; rw [← h42148 X0 X2 X1 (X1 ◇ X1)]
  have l19 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l20 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l12 X0 X1 sK2]
  have l21 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (sK2 ◇ X1) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l12 (X1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l20 X1 sK2 X0 X1]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 X1]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l18 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l24 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [l18 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK2]
    conv => enter [1]; rw [l18 (sK1 ◇ sK2) sK2 X0]
  have l26 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← l12 sK1 X0 X1]
    conv => enter [1]; rw [l24 sK1 X0 X1 sK2]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 X0 X1]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l28 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ X1) = (sK2 ◇ X2) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [l22 X0 X1 X2 X0]
    conv => enter [1]; rw [l21 X2 (X0 ◇ X1) sK2]
  have l29 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ X1) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l12 sK0 X0 X1]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l30 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l28 X0 X1 sK2 X0]
    conv => enter [1]; rw [l26 sK2 X0 sK1 sK2]
  have l31 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l30 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK2 (sK1 ◇ sK2)]
  have l32 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l31 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l29 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  have l33 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l32 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l29 sK0 (X0 ◇ X0) sK0]
  have l34 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l25 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 X0 sK0 sK2]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l33 sK1 (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← l35 y z x]

@[equational_result]
theorem Equation41_implies_Equation42149 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42149 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42149_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42149 : Equation42149 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h42149 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42149 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0)))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42149 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l1 X3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h42149 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l4 X0 sK0]
  have l8 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l6 X3 X0 X1 X3]
    conv => enter [1]; rw [← l5 X3 X1 X3 X0]
  have l9 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l10 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 (sK1 ◇ sK2) sK0]
  have l12 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK0 ◇ X0)) = (((sK1 ◇ sK2) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 X0]
    conv => enter [1, 1]; rw [l11 sK1 sK0 sK2]
  have l13 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l12 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l14 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l8 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1]; rw [← l13 sK1 sK0 X0 sK2]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 X0]
  have l16 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h42149 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1, 2, 2, 2]; rw [l15 sK1 sK2 sK2]
  have l17 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l16 sK2 sK1 X0]
    conv => enter [1]; rw [l8 X0 (sK1 ◇ sK2) (X0 ◇ (sK1 ◇ sK2))]
  have l18 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l8 X0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK2 sK1 X0]
  have l19 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l18 X0 sK1 sK2]
    conv => enter [1]; rw [← l18 X1 sK1 sK2]
  have l20 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((X0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [h4512 X1 (sK1 ◇ sK2) X2]
    conv => enter [1, 1]; rw [l19 X1 sK1 sK2 X0]
  have l21 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [l20 X1 sK1 sK2 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK2) X2]
  have l22 : ∀ X0 X2 X1 sK1 sK2 : G, (X0 ◇ X2) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 X2 X1 sK1 sK2
    conv => enter [1]; rw [← l8 X0 (sK1 ◇ sK2) X2]
    conv => enter [1]; rw [l21 X0 sK1 sK2 X2 X1]
  have l23 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l22 X1 X2 X0 X1 X1]
    conv => enter [1]; rw [l8 X0 (X1 ◇ X1) X2]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l23 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l7 X1 sK0]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK1 sK2 sK2]
    conv => enter [1]; rw [l23 (sK1 ◇ sK2) sK2 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l24 X0 sK0 sK0]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42149 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l23 X0 sK0 sK0]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l27 sK0 X0 X1]
    conv => enter [1]; rw [l8 X1 X0 (X1 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 X0 X1]
    conv => enter [1]; rw [l8 X1 X1 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 X0 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l33 y z x]

@[equational_result]
theorem Equation41_implies_Equation42151 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42151 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42151_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42151 : Equation42151 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42151 X0 X1 X0]
    conv => enter [1]; rw [← h42151 X2 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42151 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0]
    conv => enter [1]; rw [l2 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42152 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42152 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42152_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42152 : Equation42152 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42152 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42152 X2 X1 X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ X1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42152 sK0 sK0 X1 X2]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0 (X1 ◇ (sK0 ◇ X2))]
  have l4 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l3 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l1 sK0 sK0 X2]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42155 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42155 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z y]

theorem Equation4512_42155_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42155 : Equation42155 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42155 X0 X1 X0]
    conv => enter [1]; rw [← h42155 X2 X1 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = (sK2 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h42155 X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l4 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK1 ◇ sK2) X1]
  have l8 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l7 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK2]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42156 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42156 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42156_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42156 : Equation42156 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42156 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42156 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42156 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (X1 ◇ X2)) X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK2 ◇ X0) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 sK1 sK2 X0 (sK1 ◇ sK2)]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42157 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42157 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_42157_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42157 : Equation42157 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 X5 : G, ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = (X5 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X3 X0 X4 X5
    conv => enter [1]; rw [h42157 (X1 ◇ (X2 ◇ (X3 ◇ X0))) X4 X5 X2]
    conv => enter [1, 2, 2, 2]; rw [← h42157 X0 X1 X2 X3]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [h42157 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X2 X1 X3 X0 X4 : G, (X2 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X2 X1 X3 X0 X4
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X2 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h42157 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42157 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X4 ◇ X0)]
  have l5 : ∀ X2 X1 X3 X0 X4 : G, (X2 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X2 X1 X3 X0 X4
    conv => enter [1]; rw [l2 X2 X1 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l6 : ∀ X1 X2 X3 X0 X4 : G, ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = (X1 ◇ X4) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [l0 X1 X2 X3 X0 X4 X1]
    conv => enter [1]; rw [← h42157 X1 X4 X1 X0]
  have l7 : ∀ X0 X1 X4 X3 : G, (X0 ◇ X1) = ((X4 ◇ X0) ◇ (X3 ◇ X1)) := by
    intro X0 X1 X4 X3
    conv => enter [1]; rw [l4 X0 X1 X0 X3 X4]
    conv => enter [1]; rw [← l1 (X4 ◇ X0) X3 X1 X0 X3]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l5 X2 X1 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X0)) X4]
  have l9 : ∀ X1 X4 X2 X3 X0 : G, (X1 ◇ X4) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) := by
    intro X1 X4 X2 X3 X0
    conv => enter [1]; rw [← l6 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X0)) X4]
  have l10 : ∀ X0 X1 X4 X3 : G, (X0 ◇ X1) = (X4 ◇ (X0 ◇ (X3 ◇ X1))) := by
    intro X0 X1 X4 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X3]
    conv => enter [1]; rw [← h4512 X4 X0 (X3 ◇ X1)]
  have l11 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ X0) X4]
  have l12 : ∀ X1 X4 X2 X3 X0 : G, (X1 ◇ X4) = (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) := by
    intro X1 X4 X2 X3 X0
    conv => enter [1]; rw [l9 X1 X4 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ X0) X4]
  have l13 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l11 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← h42157 X4 X1 X0 (X0 ◇ X0)]
  have l14 : ∀ X1 X4 X2 : G, (X1 ◇ X4) = (X2 ◇ X4) := by
    intro X1 X4 X2
    conv => enter [1]; rw [l12 X1 X4 X2 X1 X1]
    conv => enter [1]; rw [← l10 X2 X4 X1 (X1 ◇ X1)]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0 X1]
    conv => enter [1]; rw [l13 sK0 X1 sK0]
  have l17 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK0 sK2 sK0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l19 y z x]

@[equational_result]
theorem Equation41_implies_Equation42159 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42159 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK3 sK2]
    conv => enter [1, 2]; rw [l3 sK3 sK2 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_42159_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42159 : Equation42159 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42159 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42159 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42159 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42160 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42160 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42160_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42160 : Equation42160 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42160 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42160 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42160 sK0 sK0 X1 X2]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (X2 ◇ X2)) X1]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42160 X0 X1 (sK0 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 (X0 ◇ X0) X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42161 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42161 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK4 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 sK3]
    conv => enter [1, 2]; rw [l3 sK4 sK3 sK4 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

theorem Equation4512_42161_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42161 : Equation42161 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X1 X0 : G, (X2 ◇ X3) = (X1 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [h42161 X2 X3 X1 X3 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42161 X0 X1 X3 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42161 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42161 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0 X1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ sK1) sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42162 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42162 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h41 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l2 x z y w]

theorem Equation4512_42162_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42162 : Equation42162 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42162 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42162 X0 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0 X0]
    conv => enter [1]; rw [← h42162 X0 (sK0 ◇ sK0) sK0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42162 X0 X1 X0 X0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l3 X0 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X1 X0]
    conv => enter [1]; rw [← l6 X0 sK0 X1]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1 sK0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) X1 sK0]
  have l9 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42162 (sK0 ◇ sK0) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 sK0 X2]
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l11 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l10 sK0 X0 X2]
    conv => enter [1]; rw [← h42162 sK0 X2 X0 sK0]
  have l12 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ X0) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h42162 X1 X2 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l11 sK0 (X2 ◇ (X1 ◇ (X1 ◇ X1))) X0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42164 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42164 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42164_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42164 : Equation42164 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h42164 (sK0 ◇ sK0) X1 (sK0 ◇ X0) X2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42164 sK0 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X3 X0 X1 X4 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X0 X1 X4 X2
    conv => enter [1]; rw [h42164 X3 (X0 ◇ X1) X4 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
    conv => enter [1]; rw [← h42164 (sK0 ◇ sK0) X1 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l1 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l6 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l5 sK0 X1 sK0 X2]
    conv => enter [1, 2]; rw [← l3 (sK0 ◇ sK0) X1 X2 sK0 sK0]
  have l7 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l6 sK0 X1 X2]
    conv => enter [1, 2]; rw [← l4 sK0 (X1 ◇ X2)]
  have l8 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X2)]
  have l9 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l8 sK0 X1 X2]
    conv => enter [1]; rw [← l4 sK0 (X1 ◇ X2)]
  have l10 : ∀ sK0 X1 X2 : G, (sK0 ◇ X1) = (sK0 ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l4 sK0 X1]
    conv => enter [1]; rw [l9 sK0 X1 X2]
  have l11 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ X0) = (sK0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro X2 X0 sK0 X1
    conv => enter [1]; rw [h42164 X2 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0))))]
  have l12 : ∀ sK0 X0 X2 : G, (sK0 ◇ X0) = (X2 ◇ X0) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l10 sK0 X0 (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l11 X2 X0 sK0 sK0]
  have l13 : ∀ X1 X3 X2 sK0 X0 : G, (X1 ◇ X3) = (X2 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X3 X2 sK0 X0
    conv => enter [1]; rw [h42164 X1 X3 X2 X0]
    conv => enter [1, 2]; rw [l12 X3 (X0 ◇ (X1 ◇ X2)) sK0]
  have l14 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l12 sK1 (sK2 ◇ X0) sK0]
  have l15 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ sK2) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l14 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK2 X0]
  have l16 : ∀ X1 X3 sK0 : G, (X1 ◇ X3) = (X1 ◇ sK0) := by
    intro X1 X3 sK0
    conv => enter [1]; rw [l13 X1 X3 X1 sK0 X1]
    conv => enter [1]; rw [← h42164 X1 sK0 X1 X1]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK1 sK2 X0 sK1]
  have l18 : ∀ X1 X3 sK0 : G, (X1 ◇ X3) = (sK0 ◇ sK0) := by
    intro X1 X3 sK0
    conv => enter [1]; rw [l16 X1 X3 sK0]
    conv => enter [1]; rw [l12 X1 sK0 sK0]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = (sK0 ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [l12 (sK1 ◇ sK2) X0 sK0]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l20 y z x]

@[equational_result]
theorem Equation41_implies_Equation42165 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42165 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42165_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42165 : Equation42165 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ X1) = (X2 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h42165 sK0 X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42165 X1 X2 X3 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h42165 X0 X1 (X1 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42165 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42165 X0 X1 X0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 ((sK0 ◇ sK0) ◇ X0) X1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l0 sK0 X1 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ X2) = (X3 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h42165 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [l6 X2 (X0 ◇ (X1 ◇ X0)) sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (X1 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 X1 sK0 X1]
    conv => enter [1]; rw [← h42165 X1 sK0 X1 X1]
  have l9 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l8 X1 X2 sK0]
    conv => enter [1]; rw [l6 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42166 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42166 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42166_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42166 : Equation42166 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42166 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X0 ◇ X5)))]
  have l1 : ∀ X0 X1 X4 X3 : G, (X0 ◇ X1) = (X4 ◇ X3) := by
    intro X0 X1 X4 X3
    conv => enter [1]; rw [l0 X0 X1 X0 X3 X4 X0]
    conv => enter [1]; rw [← h42166 X4 X3 X0 X1 (X0 ◇ X0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42167 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42167 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42167_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42167 : Equation42167 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42167 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42167 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X1 ◇ X0)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42167 X0 X1 X0 X0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK0 X1 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42167 (sK0 ◇ sK0) sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0]
  have l13 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 sK0 X1]
    conv => enter [1, 2]; rw [← l3 X1 (sK0 ◇ sK0) sK0]
  have l14 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 X1]
    conv => enter [1]; rw [← l3 X1 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X1]
  have l16 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42167 (sK0 ◇ sK0) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l16 sK0 X0 sK0 X2]
    conv => enter [1]; rw [← l3 X0 (X2 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l17 sK0 X0 X2]
    conv => enter [1]; rw [← l3 X2 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 X0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) X0 sK0]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42167 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l21 y z x]

@[equational_result]
theorem Equation41_implies_Equation42169 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42169 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42169_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42169 : Equation42169 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42169 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42169 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42169 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 X1 sK0 X2]
    conv => enter [1]; rw [l1 sK0 X1 (X2 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
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
theorem Equation41_implies_Equation42170 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42170 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42170_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42170 : Equation42170 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42170 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42170 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42170 X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
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
theorem Equation41_implies_Equation42171 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42171 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42171_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42171 : Equation42171 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42171 X2 X3 X4 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42171 X0 X1 X3 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42171 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42171 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42171 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 (X2 ◇ (X3 ◇ X2))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42172 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42172 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42172_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42172 : Equation42172 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42172 (sK0 ◇ X0) X1 (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X4 X0 X1 X3 X2 : G, (X4 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X0 X1 X3 X2
    conv => enter [1]; rw [h42172 X4 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42172 X1 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l4 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l3 X1 sK0 X1]
    conv => enter [1]; rw [← h42172 X1 sK0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ X0) ◇ X1) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 (sK1 ◇ sK2) sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l16 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l6 (sK1 ◇ sK2) sK0 X0 sK0]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2) sK0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0) sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42172 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l21 sK0 (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l22 y z x]

@[equational_result]
theorem Equation41_implies_Equation42174 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42174 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK3) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [h41 sK3 sK2 (sK0 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z y w]

theorem Equation4512_42174_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42174 : Equation42174 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42174 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42174 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42174 X0 X1 (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42175 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42175 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42175_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42175 : Equation42175 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42175 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42175 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42175 X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X2 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
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
theorem Equation41_implies_Equation42176 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42176 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42176_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42176 : Equation42176 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42176 X2 X3 X4 X1 (X3 ◇ X2)]
    conv => enter [1, 2]; rw [← h42176 X0 X1 X3 X4 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42176 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42176 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42176 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 (X2 ◇ (X2 ◇ X2))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42177 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42177 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_42177_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42177 : Equation42177 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = (X4 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1]; rw [h42177 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X3 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h42177 X0 X1 X5 X2]
  have l1 : ∀ sK2 X0 X1 X2 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 X2 sK1
    conv => enter [1]; rw [h42177 (sK2 ◇ X0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42177 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X4 ◇ X0)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42177 X0 X1 X0 X0]
  have l4 : ∀ sK2 X0 X1 X2 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 X2 sK1
    conv => enter [1]; rw [h4512 sK2 X0 X1]
    conv => enter [1]; rw [l1 sK2 X0 X1 X2 sK1]
  have l5 : ∀ X4 X3 X5 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X4 X3 X5 X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X2 X0 X3 X4 X5]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
  have l6 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l4 sK2 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← l3 X1 (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) sK2]
  have l7 : ∀ X4 X3 X5 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := by
    intro X4 X3 X5 X0 X1 X2
    conv => enter [1]; rw [l5 X4 X3 X5 X0 X1 X2]
    conv => enter [1]; rw [← l3 (X2 ◇ (X2 ◇ X0)) X3 X1]
  have l8 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l6 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l3 sK1 ((sK1 ◇ sK2) ◇ X0) X1]
  have l9 : ∀ X4 X3 X5 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X4 X3 X5 X0 X1 X2
    conv => enter [1]; rw [l7 X4 X3 X5 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [← l8 sK2 X0 X1 sK1]
  have l11 : ∀ X4 X3 X5 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) = ((X2 ◇ X0) ◇ X3) := by
    intro X4 X3 X5 X0 X1 X2
    conv => enter [1]; rw [l9 X4 X3 X5 X0 X1 X2]
    conv => enter [1]; rw [← l3 (X2 ◇ X0) X3 X2]
  have l12 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X0) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l3 X0 X1 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 X0 X1]
  have l13 : ∀ X3 X5 X0 X1 X2 : G, (X3 ◇ (X5 ◇ (X0 ◇ X1))) = ((X2 ◇ X0) ◇ X3) := by
    intro X3 X5 X0 X1 X2
    conv => enter [1, 2]; rw [l3 X5 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l11 X3 X3 X5 X0 X1 X2]
  have l14 : ∀ X3 X5 X0 X1 sK1 sK2 X2 : G, (X3 ◇ (X5 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ (X2 ◇ X0)) := by
    intro X3 X5 X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [l13 X3 X5 X0 X1 X2]
    conv => enter [1]; rw [l12 (X2 ◇ X0) X3 sK1 sK2]
  have l15 : ∀ X2 X0 X3 X5 X1 : G, (X2 ◇ X0) = (X3 ◇ (X5 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X5 X1
    conv => enter [1]; rw [l3 X2 X0 (X2 ◇ X2)]
    conv => enter [1]; rw [← l14 X3 X5 X0 X1 X2 X2 X2]
  have l16 : ∀ X2 X0 X5 X1 : G, (X2 ◇ X0) = (X5 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X5 X1
    conv => enter [1]; rw [l15 X2 X0 X2 X5 X1]
    conv => enter [1]; rw [← l3 X5 (X0 ◇ X1) X2]
  have l17 : ∀ X2 X0 sK1 sK2 X5 : G, (X2 ◇ X0) = ((sK1 ◇ sK2) ◇ X5) := by
    intro X2 X0 sK1 sK2 X5
    conv => enter [1]; rw [l16 X2 X0 X5 X2]
    conv => enter [1]; rw [l12 X5 (X0 ◇ X2) sK1 sK2]
  have l18 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42177 X0 X1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l17 sK1 sK2 sK1 sK2 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [l18 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42179 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42179 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ (sK0 ◇ sK3))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_42179_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42179 : Equation42179 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42179 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42179 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42179 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X2 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 X1 sK0 X2]
    conv => enter [1]; rw [l1 sK0 X1 (X2 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
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
theorem Equation41_implies_Equation42180 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42180 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK2]
  have l4 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_42180_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42180 : Equation42180 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42180 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42180 X2 X1 X0 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X0 X1 X2 sK2 sK1 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK2 sK1
    conv => enter [1]; rw [h42180 X0 X1 X2 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ X1) = (X2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l4 X0 X1 X2 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK1 ◇ sK2) X1]
  have l8 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ X1) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 X0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42181 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42181 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_42181_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42181 : Equation42181 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42181 X2 X3 X4 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42181 X0 X1 X3 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42181 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42181 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 sK1 sK2]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42181 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 (X2 ◇ (X2 ◇ X2))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42182 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42182 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_42182_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42182 : Equation42182 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X1 X3 X4 X0 X5 : G, (X2 ◇ ((X1 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = ((X0 ◇ X1) ◇ X5) := by
    intro X2 X1 X3 X4 X0 X5
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X3 ◇ (X4 ◇ X0))) X5]
    conv => enter [1, 1]; rw [← h42182 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X5 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42182 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X5 ◇ X0)))]
  have l3 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h42182 X0 sK0 (sK0 ◇ sK0) X1 X2]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X2 ◇ X0))]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0 X0 X0]
    conv => enter [1]; rw [← h42182 X0 (sK0 ◇ sK0) sK0 X0 X0]
  have l5 : ∀ X0 X1 X5 X3 : G, (X0 ◇ X1) = ((X5 ◇ X0) ◇ X3) := by
    intro X0 X1 X5 X3
    conv => enter [1]; rw [l2 X0 X1 X0 X3 X0 X5]
    conv => enter [1]; rw [← h42182 (X5 ◇ X0) X3 X0 X1 X0]
  have l6 : ∀ X2 X1 X3 X4 X0 X5 : G, (X2 ◇ ((X1 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = (X0 ◇ (X1 ◇ X5)) := by
    intro X2 X1 X3 X4 X0 X5
    conv => enter [1]; rw [l1 X2 X1 X3 X4 X0 X5]
    conv => enter [1]; rw [← h4512 X0 X1 X5]
  have l7 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X2 ◇ (X1 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X5))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [← l6 X2 X1 X3 X4 X0 X5]
    conv => enter [1, 2]; rw [← h4512 X1 (X3 ◇ (X4 ◇ X0)) X5]
  have l8 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X2 ◇ (X1 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X5)))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [l7 X0 X1 X5 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X4 ◇ X0) X5]
  have l9 : ∀ X0 X1 X5 : G, (X0 ◇ (X1 ◇ X5)) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [l8 X0 X1 X5 X0 X0 X0]
    conv => enter [1]; rw [← h42182 X5 X1 X0 X0 (X0 ◇ X0)]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
  have l13 : ∀ sK0 X0 X1 X2 sK2 : G, (sK0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [h42182 sK0 X0 X1 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l12 sK0 sK2 sK0]
  have l14 : ∀ sK2 X0 sK0 : G, (sK2 ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h42182 sK2 X0 sK2 sK2 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 sK2 sK2 sK2]
  have l15 : ∀ X2 sK2 X3 sK0 X0 X1 : G, (X2 ◇ sK2) = (X3 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 sK2 X3 sK0 X0 X1
    conv => enter [1]; rw [h42182 X2 sK2 X3 X0 X1]
    conv => enter [1, 2]; rw [l14 sK2 (X0 ◇ (X1 ◇ X2)) sK0]
  have l16 : ∀ X2 sK0 sK2 : G, (X2 ◇ sK0) = (X2 ◇ sK2) := by
    intro X2 sK0 sK2
    conv => enter [1]; rw [h42182 X2 sK0 X2 X2 X2]
    conv => enter [1]; rw [← l15 X2 sK2 X2 sK0 X2 X2]
  have l17 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42182 X2 X3 (X2 ◇ X0) X2 X2]
    conv => enter [1]; rw [← l5 X0 X1 X2 (X3 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l18 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l17 X0 X1 sK1 X0]
    conv => enter [1]; rw [l16 sK1 X0 sK2]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l19 y z x]

@[equational_result]
theorem Equation41_implies_Equation42184 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42184 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ (sK0 ◇ sK4))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_42184_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42184 : Equation42184 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42184 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42184 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42184 sK0 sK0 X1 X2 X3]
  have l3 : ∀ sK0 X2 X3 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X3 ◇ X1))) := by
    intro sK0 X2 X3 X1
    conv => enter [1]; rw [l2 sK0 X1 X2 X3]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ (X3 ◇ X1)) X1]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42184 X0 X1 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l3 sK0 X1 X0 (X0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation42185 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42185 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_42185_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42185 : Equation42185 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42185 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42185 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (X2 ◇ (X3 ◇ X2)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42185 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X3 ◇ X2))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l3 sK0 sK0 X2 X3]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ (X3 ◇ X2)) sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← l2 sK1 sK2 (X0 ◇ sK2) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42186 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42186 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK1]
  have l4 : ∀ sK0 sK4 sK3 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK0 sK3 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK0 sK4 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

theorem Equation4512_42186_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42186 : Equation42186 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42186 X2 X3 X4 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42186 X0 X1 X3 (X2 ◇ X2) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42186 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42186 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42186 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 (X2 ◇ (X2 ◇ X2))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l4 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation41_implies_Equation42187 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42187 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK4 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK4 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l2 x y z w u v]

theorem Equation4512_42187_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42187 : Equation42187 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42187 X2 X3 X4 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42187 X0 X1 X3 X2 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42187 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42187 X2 X1 X0 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42187 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← l0 X2 X3 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42265 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42265 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w]

theorem Equation4512_42265_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42265 : Equation42265 G) : Equation41 G := by
  have l0 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h42265 sK0 (sK0 ◇ X2) X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l1 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l0 X0 X1 sK0 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X2 X0 X1]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h42265 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK0 X2]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42265 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation42267 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42267 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42267_implies_Equation41 (G : Type*) [Magma G] (h42267 : Equation42267 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42267 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42267 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42267 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42268 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42268 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42268_implies_Equation41 (G : Type*) [Magma G] (h42268 : Equation42268 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42268 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42268 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42268 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42269 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42269 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42269_implies_Equation41 (G : Type*) [Magma G] (h42269 : Equation42269 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42269 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42269 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42269 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42270 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42270 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42270_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42270 : Equation42270 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h42270 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ sK0) = (X1 ◇ (X2 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42270 (sK0 ◇ X0) sK0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42270 (sK0 ◇ X0) (sK0 ◇ sK0) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h42270 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42270 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42270 X0 X1 X0 X0]
  have l7 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l3 sK0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l8 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l4 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [← l6 X1 ((sK1 ◇ sK2) ◇ sK1) sK1]
  have l10 : ∀ sK0 X0 X2 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 X0 sK0 X2]
    conv => enter [1]; rw [← l6 X2 (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) sK0]
  have l11 : ∀ sK0 X0 X2 : G, ((sK0 ◇ X0) ◇ sK0) = (X2 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X0 sK0 X2]
    conv => enter [1]; rw [← l6 X2 (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) sK0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 (sK1 ◇ sK2) sK1 sK1]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0]
    conv => enter [1]; rw [← h42270 X0 (sK0 ◇ sK0) sK0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 X0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l6 X0 (sK0 ◇ sK0) sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42270 (sK0 ◇ sK0) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l21 sK0 X0 sK0 X2]
    conv => enter [1]; rw [← l6 X2 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l18 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42270 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l26 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [l27 (sK1 ◇ sK2) sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l28 y z x]

@[equational_result]
theorem Equation41_implies_Equation42272 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42272 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42272_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42272 : Equation42272 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [h42272 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42272 sK0 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42272 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42272 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1]; rw [← h42272 (sK0 ◇ sK0) X0 sK0 sK0]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l3 X0 X1 X0 X0 X3]
    conv => enter [1]; rw [← l1 X3 X0 X1 X0 X0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l5 sK0 X0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 (sK0 ◇ X0) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 X0 sK0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42272 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ (X0 ◇ (X1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42273 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42273 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42273_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42273 : Equation42273 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42273 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42273 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42273 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X1 ◇ X4)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42273 X0 X1 X0 X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l3 X0 ((sK1 ◇ sK2) ◇ X0) sK1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l3 X0 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) X0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) X0 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42273 X0 X1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l6 sK1 sK2 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42273 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42274 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42274 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42274_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42274 : Equation42274 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42274 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X1 ◇ X5)))]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X0) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X4 X0]
    conv => enter [1]; rw [← h42274 X4 X0 X0 X0 (X1 ◇ X0)]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [l1 X0 sK0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation42275 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42275 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42275_implies_Equation41 (G : Type*) [Magma G] (h42275 : Equation42275 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42275 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42275 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42275 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42277 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42277 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK3) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h41 sK3 sK0 (sK1 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w x]

@[equational_result]
theorem Equation42277_implies_Equation41 (G : Type*) [Magma G] (h42277 : Equation42277 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42277 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42277 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42277 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42278 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42278 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42278_implies_Equation41 (G : Type*) [Magma G] (h42278 : Equation42278 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42278 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42278 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42278 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42279 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42279 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42279_implies_Equation41 (G : Type*) [Magma G] (h42279 : Equation42279 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42279 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42279 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42279 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42280 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42280 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42280_implies_Equation41 (G : Type*) [Magma G] (h42280 : Equation42280 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42280 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42280 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42280 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42282 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42282 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42282_implies_Equation41 (G : Type*) [Magma G] (h42282 : Equation42282 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42282 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42282 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42282 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42283 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42283 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42283_implies_Equation41 (G : Type*) [Magma G] (h42283 : Equation42283 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42283 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42283 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42283 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42284 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42284 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42284_implies_Equation41 (G : Type*) [Magma G] (h42284 : Equation42284 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42284 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42284 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42284 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42285 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42285 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK0 ◇ sK2)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

end Semigroup5
