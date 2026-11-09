import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41602_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41621 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41602 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41602 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41602 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41602 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 X0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 (sK0 ◇ sK0) sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h41602 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l27 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation4512_41602_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41547 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41602 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0 sK1]
    conv => enter [1]; rw [← h41602 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41602 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l10 sK0 X0]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41602 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 X0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l26 x y]

theorem Equation4512_41602_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41602 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h41602 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_41602_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41538 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) X0]
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
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41602 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41602 (sK1 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41602 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41602 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41602 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l7 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK1)]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 sK1]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK1 sK1]
  have l18 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l16 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l16 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [← l18 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
  have l23 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41602 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK1 X0]
  have l24 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l23 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1)))]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l24 sK1 X0 X1]
    conv => enter [1, 2]; rw [l4 sK1 (X1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l25 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l19 sK1 (X1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l26 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK1]
  have l28 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l27 sK1 X0]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l21 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l29 sK1]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41602 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← l28 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y
  conv => enter [1]; rw [l35 x y]
  conv => enter [1]; rw [l31 y x]

theorem Equation4512_41602_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41602 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_41602_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation41534 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41602 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41602 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41602 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK0 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41602 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation4512_41602_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation53904 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h41602 (sK2 ◇ sK2) X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK2) X0]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41602 sK2 (sK2 ◇ sK2) sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2]
  have l4 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41602 sK2 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41602 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 sK0]
    conv => enter [1]; rw [l0 sK2 ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2)]
  have l7 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l6 sK2 sK2]
    conv => enter [1]; rw [← l2 sK2 sK2 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l7 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l9 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l10 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l5 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l11 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l12 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41602 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l5 sK2 X0]
  have l13 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41602 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK2 X0]
  have l14 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l13 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2)))]
  have l15 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l12 X0 sK2]
    conv => enter [1]; rw [← l5 sK2 X0]
  have l16 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l11 sK2]
    conv => enter [1, 2]; rw [← l7 sK2]
  have l17 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← l10 sK2 (sK2 ◇ sK2) sK2]
  have l18 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l17 sK2 X0]
  have l19 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l15 X0 sK2]
  have l20 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l16 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l21 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l18 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l18 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l8 sK0 sK2]
  have l23 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l18 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l9 sK1 sK0 sK2]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1))]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l20 sK2 sK1]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
    conv => enter [1]; rw [← l21 sK2 sK1 (sK0 ◇ sK1)]
  have l27 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l22 sK2 sK2]
    conv => enter [1]; rw [l26 sK2 sK2 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l28 x y z]
  conv => enter [1]; rw [l23 z y x]

theorem Equation4512_41602_implies_Equation53922 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation53922 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41602 sK2 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41602 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l0 sK1 sK2 (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l4 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK2) X0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41602 X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK2 X0]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 X0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l6 X0 sK1 sK2]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK2)) sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l6 sK2 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41602_implies_Equation54273 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation54273 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41602 (sK1 ◇ sK1) X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41602 sK1 (sK1 ◇ sK1) sK2]
    conv => enter [1, 2, 2]; rw [← l1 sK2 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41602 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK1]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l4 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41602 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 X0]
  have l10 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41602 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 X0]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l10 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 (sK1 ◇ sK1) sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK2 sK1]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41602 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK2)]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1, 1]; rw [← l16 sK1 sK2]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l19 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l16 y x]
  conv => enter [1]; rw [← l20 z y x]

theorem Equation4512_41602_implies_Equation54243 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41602 : Equation41602 G) : Equation54243 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41602 sK2 (sK2 ◇ sK2) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l4 sK0 sK1 sK2]
  have l6 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h41602 (sK2 ◇ sK2) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2 X0]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41602 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 sK2 (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2))]
  have l9 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2 sK2 sK2]
    conv => enter [1]; rw [← l6 sK2 sK2 sK2 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l9 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l11 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l7 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l12 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41602 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l7 sK2 X0]
  have l13 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41602 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK2 X0]
  have l14 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l13 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2)))]
  have l15 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l12 X0 sK2]
    conv => enter [1]; rw [← l7 sK2 X0]
  have l16 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← l11 sK2 (sK2 ◇ sK2) sK2]
  have l17 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l9 sK2]
    conv => enter [1]; rw [l16 sK2 X0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l15 (sK0 ◇ sK1) sK2]
  have l19 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l17 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l10 sK1 sK2]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l20 z x y]

theorem Equation4512_41685_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
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

theorem Equation4512_41685_implies_Equation41585 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41585 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41685 X0 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l0 (X1 ◇ (X0 ◇ X1)) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_41685_implies_Equation41592 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41592 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0 sK1]
  have l4 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [← l2 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 X2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_41685_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41548 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l4 sK1 X2 sK1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41685 X0 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l0 (X1 ◇ (X0 ◇ X1)) sK0]
  have l8 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l7 sK1 X1 sK0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation41685_implies_Equation41550 (G : Type*) [Magma G] (h41685 : Equation41685 G) : Equation41550 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41685 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41685_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41621 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l3 sK1 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK1]
  have l6 : ∀ sK1 sK0 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [← l3 sK1 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 X2 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l8 x y]
  conv => enter [1]; rw [l7 y x]

theorem Equation4512_41685_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41547 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l6 : ∀ sK1 sK0 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [← l3 sK1 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 X2 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l8 x y]
  conv => enter [1]; rw [l7 y x]

theorem Equation4512_41685_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41557 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l1 (X2 ◇ (X1 ◇ X2)) X0]
  have l4 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l5 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 X2 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 (sK1 ◇ sK0) sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK0) sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ sK0) sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_41685_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41538 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
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
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l8 y x]

@[equational_result]
theorem Equation41685_implies_Equation41628 (G : Type*) [Magma G] (h41685 : Equation41685 G) : Equation41628 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 X2 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_41685_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation41534 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 X2 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_41685_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation53904 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l3 : ∀ sK2 X1 X2 : G, (sK2 ◇ sK2) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK2 X1 X2
    conv => enter [1]; rw [l2 sK2 X1 X2]
  have l4 : ∀ X1 X2 sK2 : G, (X1 ◇ X1) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK2]
  have l5 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l4 sK2 X2 sK2]
  have l6 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l7 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l5 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1, 2]; rw [l5 sK2 sK0]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) sK1]
  have l10 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1]
    conv => enter [1, 2, 1]; rw [← l8 sK2 sK1 sK0]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK2 sK1]
    conv => enter [1]; rw [← l7 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]
  conv => enter [1]; rw [l8 z y x]

theorem Equation4512_41685_implies_Equation53922 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation53922 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 (X1 ◇ X2)]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 (sK1 ◇ sK2) X0]
  have l4 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1]; rw [← l3 sK1 sK2 X1]
  have l5 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X1]
  have l6 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 X2 sK1 sK2]
  have l7 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK2)) sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_41685_implies_Equation54273 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation54273 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l3 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l2 sK1 X1 X2]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l4 sK1 X2 sK1]
  have l6 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l7 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l8 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l3 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l8 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← l7 sK1 X0 X0]
  have l10 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l9 sK2 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 X0 (sK2 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l11 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [← l12 z y x]

theorem Equation4512_41685_implies_Equation54243 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41685 : Equation41685 G) : Equation54243 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41685 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41685 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41685 X1 X2 (X2 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X2 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK2]
  have l4 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X1]
  have l5 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 X2 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l6 z x y]

theorem Equation4512_41597_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h41597 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41597 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l27 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l24 sK0 X0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0 X0]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l27 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41597 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← h41597 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
  have l30 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 (X0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h41597 sK0 X0 sK1]
  have l31 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l33 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l31 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK0]
  have l34 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l33 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l25 sK0 sK1]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l34 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l35 X0 sK0 sK1]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) X0]
  have l37 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l36 X0 sK0 sK1]
  have l38 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 sK0]
    conv => enter [1]; rw [l38 sK0 sK0 X0]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2, 2]; rw [← l39 sK0 X0]
  have l41 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l42 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l41 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l44 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0]
  have l45 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l44 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l46 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l28 sK0 X0 sK1]
  have l47 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l46 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l45 sK0 X0 X0]
  have l48 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l47 X0 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 X0 X0]
  have l49 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41597 X1 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l48 (X0 ◇ X1) sK0]
  have l50 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l49 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))]
  have l51 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l50 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l42 sK0 (X0 ◇ X1) X1]
  have l52 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l51 X1 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 (X0 ◇ X1) X0]
  have l53 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l52 X1 sK0 X0]
    conv => enter [1]; rw [l48 X1 sK0]
  have l54 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [l52 X1 sK0 X0]
  have l55 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l54 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
  have l56 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← l53 sK0 (sK0 ◇ X1) X2]
    conv => enter [1]; rw [← l55 X1 X2 sK0 sK0]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l56 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1]; rw [← l57 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l58 x y]

theorem Equation4512_41597_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation41621 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2]; rw [l7 sK1 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41597 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41597 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1, 2]; rw [h41597 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0)))]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l16 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41597 (sK1 ◇ sK0) X0 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK0 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h41597 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l25 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l26 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l30 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l31 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l30 sK0 X0 sK1]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41597 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l41 x y]
  conv => enter [1]; rw [l38 y x]

theorem Equation4512_41597_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation41547 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41597 (sK0 ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41597 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41597 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41597 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0 X0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41597 (sK1 ◇ sK0) X0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X0 X0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ X0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h41597 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l14 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41597 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l26 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l27 x y]
  conv => enter [1]; rw [l24 y x]

theorem Equation4512_41597_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h41597 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41597 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l31 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l28 sK0 X0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0 X0]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l31 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41597 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← h41597 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
  have l35 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 (X0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h41597 sK0 X0 sK1]
  have l36 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l35 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 (sK1 ◇ sK0)]
  have l39 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l36 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK0]
  have l40 : ∀ X0 sK1 sK0 : G, ((X0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l39 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l29 sK0 sK1]
  have l41 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l40 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l42 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l41 X0 sK0 sK1]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) X0]
  have l43 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l42 X0 sK0 sK1]
  have l44 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l43 sK1 sK0 X0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK0 X0]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2, 2]; rw [← l45 sK0 X0]
  have l47 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l48 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l47 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l50 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l51 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l50 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l52 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41597 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l32 sK0 X0 sK1]
  have l53 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l52 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l51 sK0 X0 X0]
  have l54 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l53 X0 X0 sK0]
    conv => enter [1]; rw [← l51 sK0 X0 X0]
  have l55 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41597 X1 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l54 (X0 ◇ X1) sK0]
  have l56 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l55 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))]
  have l57 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l56 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l48 sK0 (X0 ◇ X1) X1]
  have l58 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l57 X1 X0 sK0]
    conv => enter [1]; rw [← l51 sK0 (X0 ◇ X1) X0]
  have l59 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l58 X1 sK0 X0]
    conv => enter [1]; rw [l54 X1 sK0]
  have l60 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l58 X0 sK0 X1]
  have l61 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l60 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l62 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← l59 sK0 (sK0 ◇ X0) X2]
    conv => enter [1]; rw [l61 sK0 sK0 X0 X2]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l62 sK0 (sK1 ◇ sK0) sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1, 2]; rw [l63 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l64 x y]

theorem Equation4512_41597_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41597 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41597 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ sK0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l11 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41597 (X0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h41597 sK0 X0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41597 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 X0 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l20 X0 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41597 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h41597 sK0 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 1]; rw [← l33 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l38 x y]
  conv => enter [1]; rw [l33 y x]

theorem Equation4512_41597_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation41534 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41597 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41597 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_41597_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation53938 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41597 (X1 ◇ (X2 ◇ X0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h41597 X0 X1 X2]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) (X0 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ X0)]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41597 X0 X0 X0]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l2 X0 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l6 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l10 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l12 X1 X2 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l14 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l14 (X0 ◇ X0) X1 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l19 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 X1 X0 X0]
    conv => enter [1, 2]; rw [← l19 X0 X1 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1 X0]
    conv => enter [1]; rw [← l20 X1 X0]
  intro x y z
  conv => enter [1]; rw [l21 x y]
  conv => enter [1]; rw [l17 y z]
  conv => enter [1, 2]; rw [l17 y x]

theorem Equation4512_41597_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation53959 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41597 (X1 ◇ (X2 ◇ X0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h41597 X0 X1 X2]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) (X0 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ X0)]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41597 X0 X0 X0]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l2 X0 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l6 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l10 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l12 X1 X2 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l14 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l14 (X0 ◇ X0) X1 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l19 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 X1 X0 X0]
    conv => enter [1, 2]; rw [← l19 X0 X1 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1 X0]
    conv => enter [1]; rw [← l20 X1 X0]
  intro x y z
  conv => enter [1]; rw [l21 x y]
  conv => enter [1]; rw [l10 y]
  conv => enter [1]; rw [l2 y z]

theorem Equation4512_41597_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation54270 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41597 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41597 (X1 ◇ (X2 ◇ X0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h41597 X0 X1 X2]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) (X0 ◇ X0)]
  have l5 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ X0)]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l5 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41597 X0 X0 X0]
    conv => enter [1, 2]; rw [← l3 X0 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [← l3 X0 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l7 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l11 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [l13 X1 X2 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l15 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l15 (X0 ◇ X0) X1 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l19 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l19 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l21 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X0 X1]
    conv => enter [1, 2]; rw [← l20 X0 (X1 ◇ X2) X2]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← l21 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l18 y x]
  conv => enter [1]; rw [← l22 z x y]

theorem Equation4512_41597_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41597 : Equation41597 G) : Equation54261 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (X1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41597 ((sK0 ◇ sK1) ◇ X0) X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [l6 sK0 sK1 X0]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ X0)) = (X1 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41597 (sK1 ◇ X0) X1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l8 sK1 X0]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41597 X0 sK1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41597 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1, 2, 2]; rw [l11 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41597 (sK1 ◇ sK1) (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [l10 sK1 sK0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41597 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41597 X0 (X1 ◇ X0) X1]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41597 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))]
  have l19 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [h41597 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)))]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41597 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l8 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))]
  have l21 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ X0)) = (X1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))]
  have l26 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41597 (sK0 ◇ sK1) X0 sK1]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l30 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ X0) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l21 X0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l25 sK1 X0 X0]
  have l31 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (((sK0 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l21 X0 X0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l26 sK0 sK1 X0 X0]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l28 sK1 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l34 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [l30 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ X0)]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l31 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X0 ((sK0 ◇ sK1) ◇ X0)]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l32 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l36 sK1 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41597 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l41 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h41597 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← h41597 (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41597 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1, 2]; rw [← l38 sK1 sK0]
  have l44 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [← l41 sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l46 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l44 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l47 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l48 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [← l39 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l49 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l48 sK1 X0 sK0]
  have l50 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l46 sK1 X0]
    conv => enter [1]; rw [l49 sK1 X0 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h41597 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l27 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l27 sK0 sK1 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l14 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l54 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l50 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l51 sK0 sK1]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l59 sK0 sK1]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [← l34 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1]
    conv => enter [1]; rw [← l62 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l63 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l64 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41597 (sK0 ◇ sK1) sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h41597 sK1 (sK0 ◇ sK1) sK0]
  have l71 : ∀ X0 sK0 sK1 : G, ((X0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41597 (X0 ◇ (sK0 ◇ sK1)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h41597 sK1 X0 sK0]
  have l72 : ∀ X0 sK0 sK1 : G, ((X0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l71 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1]
    conv => enter [1]; rw [← l70 sK0 sK1]
  have l74 : ∀ X0 sK0 sK1 : G, ((X0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l72 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l43 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l73 sK1 sK0]
  have l76 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l74 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
  have l77 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l76 X0 sK1 sK0]
  have l78 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l77 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l75 sK0 sK1]
  have l79 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l78 sK0 sK1 X0]
  have l80 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l79 sK0 sK1 X0]
  have l81 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [l80 sK0 sK1 X0]
  have l82 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l37 sK2 sK1]
    conv => enter [1, 2]; rw [← l75 sK0 sK1]
  have l83 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41597 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 X0]
    conv => enter [1, 2, 2]; rw [← l81 sK0 sK1 X0]
  have l84 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l65 sK0 sK1]
    conv => enter [1]; rw [l83 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l65 sK0 sK1]
  have l85 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l84 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l66 sK0 sK1]
  have l86 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l82 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l86 z y x]

theorem Equation4512_41566_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41566 : Equation41566 G) : Equation310 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41566 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41566 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l3 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41566 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41566 X0 (X0 ◇ X1) X1]
  have l7 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41566 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41566 sK1 X0 X1]
    conv => enter [1]; rw [l3 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ X1)))]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l3 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0 X1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l9 sK1 sK1 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l14 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l21 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [l23 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation4512_41566_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41566 : Equation41566 G) : Equation41548 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41566 sK0 X0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41566 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41566 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41566 X0 (X0 ◇ X1) X1]
  have l7 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41566 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41566 sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ X1)))]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0 X1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l9 sK1 sK1 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l6 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]
  conv => enter [1]; rw [l26 x y]

theorem Equation4512_41566_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41566 : Equation41566 G) : Equation41547 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41566 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41566 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41566 X0 (X0 ◇ X1) X1]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41566 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41566 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ X1)))]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l15 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_41566_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41566 : Equation41566 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41566 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41566 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41566 X0 (X0 ◇ X1) X1]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41566 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41566 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ X1)))]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h41566 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41566 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [l24 sK1 sK0]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l24 sK1 sK0]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l29 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41566 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 sK0]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1, 2]; rw [l31 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l24 sK1 sK0]
    conv => enter [1]; rw [l36 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l31 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l33 sK0 X0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l30 sK1 sK0 sK0]
    conv => enter [1]; rw [l43 sK1 sK0]
  have l45 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1, 2]; rw [← l44 sK1 sK0]
  have l46 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l46 sK1 sK0 sK1]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l31 sK1 sK0]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l51 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l53 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 X0]
  have l54 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41566 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK1 sK0]
  have l55 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l54 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l51 sK1 sK0 sK1]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l55 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l49 sK1 sK0]
  have l57 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l40 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1]; rw [l56 sK1 sK0 X0]
  have l58 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l57 sK1 sK0 X0]
  have l59 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [l58 sK1 sK0 X0]
  have l60 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [l59 sK1 sK0 X0]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l42 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l53 sK1 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l62 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 sK0]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l65 x y]

end Semigroup5
