import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

theorem Equation3385_4512_implies_Equation3404 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3404 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h3385 (sK2 ◇ sK0) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 (sK2 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3385 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X1]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l8 : ∀ X0 sK2 sK0 : G, (X0 ◇ sK2) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h3385 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l7 X0 (sK2 ◇ sK0)]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ sK1) X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l7 (sK2 ◇ sK0) sK0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0 X0]
    conv => enter [1]; rw [l11 X0 X0 X1]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK2]
    conv => enter [1, 2]; rw [l13 sK2 X0]
  have l15 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l7 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l14 sK1 sK2 sK0 X0]
  have l16 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l7 (X0 ◇ X1) X2]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l16 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l17 sK0 ((sK2 ◇ sK0) ◇ X0) (sK1 ◇ (sK2 ◇ sK0))]
  have l20 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l19 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) X0 (sK1 ◇ (sK2 ◇ sK0))]
  have l21 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK2) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l20 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l8 (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2 sK0]
  have l22 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l21 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
  have l23 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ X0) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1, 2]; rw [l7 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK0 sK1 X0 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [l23 (sK0 ◇ sK1) sK2 sK1 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK2 sK1 sK0 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation3385_4512_implies_Equation3417 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3417 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X1]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation3385_4512_implies_Equation4364 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation4364 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3385 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3385 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 X0 sK0]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK2 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3385 (sK2 ◇ sK0) X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK0 X0 sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3385 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 X0]
  have l5 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 sK2 X1]
  have l6 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [← h3385 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation3385_4512_implies_Equation40 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3385 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 sK1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (((sK0 ◇ sK0) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK0) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X1]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X1 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK0 X0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation3385_implies_Equation3269 (G : Type*) [Magma G] (h3385 : Equation3385 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h3385 x x y]

theorem Equation3385_4512_implies_Equation3282 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3282 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3385 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 sK1 sK1 sK1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3385 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l4 sK0]
  have l6 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h3385 X1 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l2 X0 sK1]
  have l7 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l6 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l7 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h3385 X1 X0 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h3385 (sK1 ◇ sK1) sK0 sK0]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3385 X0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [l14 (sK1 ◇ sK1) sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]
  conv => enter [1]; rw [h3385 y y y]

theorem Equation3385_4512_implies_Equation3294 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3294 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3385 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 sK2]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3385 (sK2 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3385 X0 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h3385 sK1 sK2 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l5 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3385 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3385 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0 sK1]
    conv => enter [1, 2]; rw [← l2 sK2 sK1 X0]
  have l9 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = ((X0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h3385 X1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l3 X0 sK1 sK2]
  have l10 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l9 X1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK2) (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))]
  have l11 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l10 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h3385 X1 X0 (sK1 ◇ sK2)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) sK1 sK2 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) sK1 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l7 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK1 sK2 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK1 sK2 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← h3385 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0 sK0]
  have l20 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3385 X0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2, 2]; rw [← l19 sK0 sK1 sK2]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l20 X0 sK1 sK2 sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation3385_4512_implies_Equation3297 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3297 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3385 (sK2 ◇ (sK2 ◇ sK1)) X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3385 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3385 (sK2 ◇ sK1) X0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 (sK2 ◇ sK1)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l5 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [h3385 sK2 sK2 sK1]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3385 (sK2 ◇ (sK2 ◇ sK1)) sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK2 sK1]
  have l7 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [← l3 sK2 sK1 (sK2 ◇ sK1)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (((sK0 ◇ sK0) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK0) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X1 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [l11 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l7 sK2 sK1]
  have l14 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l11 sK2 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [l14 sK2 sK1]
  have l16 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 sK2]
  have l17 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l7 sK2 sK1]
    conv => enter [1]; rw [l16 sK2 sK1]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [l17 sK2 sK1]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l18 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation3385_4512_implies_Equation4305 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation4305 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X1]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((X0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h3385 (X0 ◇ sK1) X0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation3385_4512_implies_Equation4325 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation4325 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3385 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3385 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 sK0]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3385 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK2]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 X0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 X1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l6 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3385 (sK1 ◇ (sK2 ◇ sK2)) sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK2 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK2 ◇ sK2)]
  have l15 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l14 sK2 sK2 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 sK2]
  have l16 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l12 X0 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK2 X0 X0]
  have l17 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l15 sK2 sK1]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l18 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK2]
    conv => enter [1]; rw [l17 sK2 sK1]
  have l19 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 sK2 X0]
  have l20 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3385 X0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l18 sK2 sK1]
  have l21 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK1 sK2]
    conv => enter [1]; rw [← l16 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l22 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l19 X0 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l21 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 (sK2 ◇ sK2) sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation3385_4512_implies_Equation4369 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation4369 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3385 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3385 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2 X0]
  have l3 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK2 X1]
  have l4 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l3 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [← h3385 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation3385_implies_Equation4273 (G : Type*) [Magma G] (h3385 : Equation3385 G) : Equation4273 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3385 sK0 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3385 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [← h3385 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3385 X0 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l3 sK0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3385 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l18 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h3385 sK1 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3385 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h3385 (sK0 ◇ sK1) sK1 (sK0 ◇ sK1)]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3385 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK0]
    conv => enter [1, 2]; rw [← l29 sK1 sK0]
  have l33 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3385 X0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l31 sK0 sK1]
  have l34 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3385 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l33 X0 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l32 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3385 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l37 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l38 x y]

theorem Equation3385_4512_implies_Equation4297 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation4297 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3385 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X1]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK2]
    conv => enter [1]; rw [l8 sK2 sK2 (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l9 sK2 sK0 sK1]
    conv => enter [1]; rw [← h3385 (sK0 ◇ sK1) sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation3385_implies_Equation4290 (G : Type*) [Magma G] (h3385 : Equation3385 G) : Equation4290 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3385 X0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h3385 sK0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3385 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 sK0 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3385 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h3385 (sK0 ◇ sK1) sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3385 X0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation3388_implies_Equation3334 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3334 G := by
  have l0 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK1
    conv => enter [1, 2, 2]; rw [h3388 sK2 sK1 sK2]
    conv => enter [1]; rw [← h3388 X0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3388 X0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3388_implies_Equation3414 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation3414 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3388 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← h3388 X0 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3388 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3388_implies_Equation4362 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4362 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3388 X0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2, 2]; rw [← h3388 sK0 sK2 sK1]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h3388 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3388 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3388_implies_Equation4275 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4275 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3388 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h3388 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation3388_implies_Equation4320 (G : Type*) [Magma G] (h3388 : Equation3388 G) : Equation4320 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3388 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← h3388 sK0 sK0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3388 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3388 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3331_4512_implies_Equation3323 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3323 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h3331 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK2) sK2 sK2]
  have l1 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (((sK2 ◇ sK2) ◇ sK2) ◇ (X0 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h3331 X1 X0 ((sK2 ◇ sK2) ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l0 X0 sK2]
  have l2 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l1 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) sK2 (X0 ◇ sK2)]
  have l3 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l2 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK2) X0 sK2]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation3331_4512_implies_Equation3334 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ sK1) sK2 sK1]
  have l1 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3331 (sK2 ◇ (sK2 ◇ sK1)) sK2 (sK2 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X1)) = ((X0 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) X1]
    conv => enter [1, 1]; rw [← l1 X0 sK2 sK1]
  have l3 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l2 X0 sK2 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK1) X1]
  have l4 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← l3 X0 sK2 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) sK2 X1]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3331 sK2 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK1]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l4 X0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 X0 sK2 sK1]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3331_4512_implies_Equation4358 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4358 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3331 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3331 (sK1 ◇ sK2) sK1 sK2]
  have l1 : ∀ X0 sK2 X1 sK1 : G, ((X0 ◇ sK2) ◇ X1) = (X0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ X1)) := by
    intro X0 sK2 X1 sK1
    conv => enter [1, 1]; rw [l0 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK2) ◇ sK1) X1]
  have l2 : ∀ X0 sK2 X1 sK1 : G, ((X0 ◇ sK2) ◇ X1) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X1))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l1 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) sK1 X1]
  have l3 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X1))) = (X0 ◇ (sK2 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l2 X0 sK2 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 sK2 X1]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h3331 sK1 sK1 sK2]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3331 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1]; rw [l3 X0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation3331_4512_implies_Equation4270 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4270 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3331 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3331 X0 sK0 sK0]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3331 X1 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h3331 X0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ sK0) X0 sK0]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3331 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 X0 X0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x x y]

theorem Equation3331_4512_implies_Equation4283 (G : Type*) [Magma G] (h3331 : Equation3331 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3331 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3331 (sK0 ◇ sK1) sK0 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X1)) = ((X0 ◇ sK1) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK1) ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l0 X0 sK1 sK0]
  have l2 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l1 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 sK1 X1]
  have l3 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [← l2 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3331 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3331 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← l3 X0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x x y]

theorem Equation3397_4512_implies_Equation3363 (G : Type*) [Magma G] (h3397 : Equation3397 G) (h4512 : Equation4512 G) : Equation3363 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3397 X1 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h3397 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h3397 sK0 sK1 sK0]
    conv => enter [1]; rw [h3397 sK0 (sK1 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1, 2, 2]; rw [← h3397 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← h3397 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h3397 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation3317_4512_implies_Equation3320 (G : Type*) [Magma G] (h3317 : Equation3317 G) (h4512 : Equation4512 G) : Equation3320 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h3317 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3317 X0 X1 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3317 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation3398_implies_Equation3323 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation3323 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro X0 sK2
    conv => enter [1]; rw [h3398 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3398 sK2 X0 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3398 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3398 (sK1 ◇ (sK2 ◇ sK2)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3398 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3398 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3398 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation3398_4512_implies_Equation3334 (G : Type*) [Magma G] (h3398 : Equation3398 G) (h4512 : Equation4512 G) : Equation3334 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3398 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3398 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK2 X0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK1 sK0]
  have l3 : ∀ X1 X0 sK2 sK1 : G, ((X1 ◇ (X0 ◇ sK2)) ◇ sK1) = ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l1 (X1 ◇ (X0 ◇ sK2)) sK1 sK2]
    conv => enter [1, 2]; rw [← h3398 X0 X1 sK2]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l1 X0 sK1 sK2]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l3 X1 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ sK2) sK1]
  have l7 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l6 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK0]
    conv => enter [1]; rw [← h3398 sK0 sK0 sK1]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3398 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
    conv => enter [1]; rw [l7 sK2 sK1 sK0 sK0]
  have l11 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l10 sK2 sK1 sK0]
    conv => enter [1]; rw [← h3398 sK0 sK0 (sK2 ◇ sK1)]
  have l12 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l11 sK2 sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3398 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation3398_implies_Equation3414 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation3414 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h3398 X0 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3398 sK2 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3398 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3398_implies_Equation40 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3398 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3398 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK1 X0 sK1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3398 X0 X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← h3398 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation3398_implies_Equation3269 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h3398 x x y]

@[equational_result]
theorem Equation3398_implies_Equation3282 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation3282 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3398 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3398 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK1 X0 sK1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3398 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h3398 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1]
    conv => enter [1, 1]; rw [← h3398 sK1 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← l1 X0 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3398 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l1 X0 sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3398 X0 X0 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 X0]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l6 X0 sK1]
    conv => enter [1]; rw [l4 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]
  conv => enter [1]; rw [h3398 y y y]

@[equational_result]
theorem Equation3398_implies_Equation3297 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation3297 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3398 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK0]
  have l1 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3398 X0 (sK2 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h3398 sK1 X0 (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3398 sK1 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3398 sK2 sK1 (sK2 ◇ sK1)]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3398 (sK2 ◇ (sK2 ◇ sK1)) X0 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3398 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK2 sK1 X0]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3398 sK2 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK1]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3398 sK2 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK2 sK1]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h3398 sK2 sK2 sK1]
    conv => enter [1]; rw [l7 sK2 sK1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK2]
  have l10 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h3398 X0 (sK2 ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1, 2]; rw [← l5 sK1 (X0 ◇ X1) sK2]
  have l11 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ sK1) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l10 X0 sK2 sK1 X0]
    conv => enter [1]; rw [← h3398 X0 sK1 X0]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3398 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [← l1 X0 sK2 sK1]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l11 X0 sK2 sK1]
  have l14 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 X0]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h3398 X0 X0 sK1]
    conv => enter [1, 2]; rw [l14 X0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l15 (sK0 ◇ sK0) sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

@[equational_result]
theorem Equation3398_implies_Equation4369 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h3398 X0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3398 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3398 sK1 X0 sK2]
  have l2 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h3398 X0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3398 sK2 X0 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 (sK2 ◇ (sK1 ◇ sK0)) sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h3398 sK1 sK2 sK0]
  have l4 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h3398 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l3 sK2 sK1 sK0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3398 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 X0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3398 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [← h3398 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3398 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [← h3398 sK0 sK0 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l9 sK0 sK2 sK0]
    conv => enter [1]; rw [← l1 sK2 sK2 sK0]
  have l11 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l10 sK2 sK0]
  have l12 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1 sK0]
    conv => enter [1]; rw [l5 sK2 sK1 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l12 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation3398_implies_Equation4297 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation4297 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3398 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h3398 X0 X0 sK1]
  have l3 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 sK2 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3398_implies_Equation4290 (G : Type*) [Magma G] (h3398 : Equation3398 G) : Equation4290 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3398 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3398 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l0 X0 sK1 sK0]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3398 X0 X0 sK1]
    conv => enter [1, 2]; rw [l1 X0 sK1 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 sK0]
    conv => enter [1]; rw [← h3398 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3398 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3404_4512_implies_Equation3350 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3350 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h3404 (X1 ◇ (X2 ◇ X0)) X3 X2]
    conv => enter [1, 2, 2]; rw [← h3404 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK2 ◇ sK2)) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 (sK2 ◇ sK2) X0 sK0]
  have l5 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h3404 (X0 ◇ (sK2 ◇ sK2)) X1 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK2 X0 sK2]
  have l6 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h3404 X0 X1 sK2]
    conv => enter [1]; rw [← l5 X0 sK2 X1]
  have l7 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK2 ◇ sK2)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK2 sK0 sK2]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK2 X0]
    conv => enter [1]; rw [← h3404 sK0 X0 sK2]
  have l10 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [h3404 X1 (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l9 sK0 sK2 (X0 ◇ X1)]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK2 (sK0 ◇ sK1)]
  have l12 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l13 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [← h3404 (sK2 ◇ sK2) sK0 sK0]
  have l14 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l11 sK1 sK0 sK2]
    conv => enter [1]; rw [← h3404 sK1 sK0 sK0]
  have l15 : ∀ X1 sK0 sK2 : G, (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ sK0) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [l10 X1 sK0 sK2 X1]
    conv => enter [1]; rw [← h3404 X1 sK0 X1]
  have l16 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK2) (sK2 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [l13 sK2 sK0]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2 sK0]
    conv => enter [1]; rw [← l16 sK2 sK0]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l9 sK0 sK2 sK0]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l19 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [l15 X0 sK0 sK2]
  have l20 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK2]
  have l21 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ X0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l20 sK2 X0 sK0]
    conv => enter [1]; rw [l2 (sK2 ◇ sK2) X0 sK0 sK0]
  have l22 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l21 sK2 X0 sK2]
    conv => enter [1]; rw [← h3404 X0 (sK2 ◇ sK2) sK2]
  have l23 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK2) X1 X0]
    conv => enter [1, 2, 2]; rw [← l22 sK2 X0]
  have l24 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l23 sK2 X1 X0]
    conv => enter [1, 2]; rw [← l7 X1 X0 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK2]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 (sK0 ◇ sK1) sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK2 (sK0 ◇ sK1) sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK1) sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l32 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h3404 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0 sK0]
    conv => enter [1, 2, 2]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l32 sK1 sK0 sK2 X0]
  have l34 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [h3404 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 (X0 ◇ X1) sK2]
  have l35 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3404 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l36 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l35 sK1 sK0 sK2]
    conv => enter [1]; rw [← h3404 sK1 (sK0 ◇ sK1) sK0]
  have l37 : ∀ X1 sK1 sK0 sK2 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X1 sK1 sK0 sK2
    conv => enter [1]; rw [l34 X1 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← h3404 X1 (sK0 ◇ sK1) X1]
  have l38 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK2 ◇ sK2)) sK1 sK1]
    conv => enter [1, 2]; rw [l36 sK1 sK0 sK2]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l38 sK0 sK0 sK1]
  have l40 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l33 sK0 sK1 ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) sK2]
  have l41 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK2]
  have l42 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l41 sK0 sK2 sK1]
    conv => enter [1]; rw [l37 (sK0 ◇ sK1) sK1 sK0 sK2]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3404 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK2 sK0 sK0]
    conv => enter [1]; rw [← l44 sK1 sK0]
  have l46 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l22 sK2 sK0]
    conv => enter [1]; rw [l45 sK2 sK0 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2]; rw [← l46 sK0 sK2 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 sK0]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l49 x y z]

theorem Equation3404_4512_implies_Equation3364 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3364 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK0) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK2) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK2 X0 sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK1 X0]
    conv => enter [1, 2]; rw [← h3404 (sK2 ◇ (sK0 ◇ sK2)) X0 sK1]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ sK2)) X0 (sK0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2 (sK0 ◇ sK2)]
  have l4 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK0 X0]
    conv => enter [1]; rw [← h3404 sK0 X0 (sK0 ◇ sK2)]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l4 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l6 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [h3404 X1 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l4 sK2 sK0 (X0 ◇ X1)]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3404 sK1 (sK2 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [l4 sK2 sK0 (sK0 ◇ sK1)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← h3404 sK1 sK0 sK0]
  have l9 : ∀ X1 sK2 sK0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X1 ◇ sK0) := by
    intro X1 sK2 sK0
    conv => enter [1]; rw [l6 X1 sK2 sK0 X1]
    conv => enter [1]; rw [← h3404 X1 sK0 X1]
  have l10 : ∀ sK2 sK0 X0 X1 sK1 : G, (((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK2 sK0 X0 X1 sK1
    conv => enter [1]; rw [h3404 ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 sK0 X0]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK2)) sK1 ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1)]
  have l13 : ∀ sK2 sK0 X0 X1 sK1 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK2 sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l10 sK2 sK0 X0 X1 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK0 (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))]
  have l15 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [← l4 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 sK2 sK0 X0 X1 sK1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK0 sK1 sK1 sK2]
  have l18 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0 sK0]
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l18 sK1 sK2 sK0 X0]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3404 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l21 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3404 sK2 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 (sK0 ◇ sK2) sK2]
  have l22 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [← h3404 sK2 (sK0 ◇ sK1) sK0]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← h3404 sK1 (sK0 ◇ sK1) sK0]
  have l24 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK1]
    conv => enter [1, 2]; rw [l22 sK2 sK1 sK0]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK0 sK2]
    conv => enter [1]; rw [l24 sK2 sK0 sK1]
  have l26 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ sK2)) sK1 sK1]
    conv => enter [1, 2]; rw [l23 sK1 sK2 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK0 sK1]
  have l28 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK2 sK1]
    conv => enter [1]; rw [← h3404 (sK0 ◇ sK1) sK1 sK2]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK1 sK1]
    conv => enter [1, 2]; rw [← l27 sK0 sK1]
  have l30 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l28 sK2 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [l30 sK1 sK0 sK2]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK1 sK0 sK0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation3404_4512_implies_Equation3385 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3385 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h3404 (X1 ◇ (X2 ◇ X0)) X3 X2]
    conv => enter [1, 2, 2]; rw [← h3404 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1, 2]; rw [← h3404 (sK1 ◇ sK2) X0 sK0]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2 X0]
    conv => enter [1, 2]; rw [← h3404 (sK0 ◇ (sK1 ◇ sK2)) X0 sK2]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3404 X0 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 X0]
  have l7 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h3404 (sK1 ◇ X0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X0]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK0))) = (sK1 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l7 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 X1]
  have l9 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [← l8 X0 X1 sK1 sK1]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK1 sK2]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3404 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1 sK2]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 (sK0 ◇ sK1) X0 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) ((sK0 ◇ sK1) ◇ sK0)]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) (sK0 ◇ sK1) sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h3404 sK2 (sK0 ◇ sK1) sK1]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3404 sK1 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 sK0]
  have l18 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l19 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l18 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ sK1) ◇ sK0)]
  have l20 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK1) sK0]
  have l21 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l20 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l22 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l21 sK2 sK0 sK1]
    conv => enter [1]; rw [← h3404 (sK1 ◇ sK2) sK0 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK2 sK0 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3404 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l25 sK1 sK2 sK0]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3404 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 X0 sK1 sK0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← h3404 X0 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ sK1)]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l27 sK0 sK1 X0]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ sK1)]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2 sK2]
  have l33 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l32 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 sK2 sK0 sK1]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l34 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation3364_4512_implies_Equation3350 (G : Type*) [Magma G] (h3364 : Equation3364 G) (h4512 : Equation4512 G) : Equation3350 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3364 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3364 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3364 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h3364 (sK2 ◇ sK2) X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l3 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h3364 (sK0 ◇ (sK2 ◇ sK2)) X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h3364 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) (sK0 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3364 X3 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l5 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 sK2 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))]
  have l6 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK2 X1 sK0]
  have l7 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l4 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← h3364 X3 X1 X3]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK1 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h3364 sK1 sK1 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3364 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3364 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 sK1]
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l2 sK2 (sK2 ◇ sK2) sK0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h3364 sK1 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3364 sK0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK2 ◇ sK2))]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h3364 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l21 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 sK2 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l24 sK0 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3364 sK0 sK1 sK1]
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
  have l28 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h3364 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l29 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l28 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l30 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h3364 (sK2 ◇ sK2) X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l28 sK2]
  have l31 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l30 sK2 X0]
    conv => enter [1, 2]; rw [← l28 sK2]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l29 sK0 sK2]
    conv => enter [1]; rw [← l31 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 (sK0 ◇ (sK2 ◇ sK2)) X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l34 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [l33 sK0 sK2 (sK2 ◇ sK2)]
  have l35 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← l34 sK1 sK0 sK2]
  have l36 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l35 sK0 sK2 sK1]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l31 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK0 sK1 (sK2 ◇ sK2) sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation3364_4512_implies_Equation3385 (G : Type*) [Magma G] (h3364 : Equation3364 G) (h4512 : Equation4512 G) : Equation3385 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3364 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3364 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3364 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3364 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3364 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l3 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3364 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h3364 sK1 (sK1 ◇ sK2) sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3364 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h3364 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3364 X3 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l6 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h3364 sK1 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l7 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h3364 sK1 X1 sK1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 X1 sK1]
  have l10 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l5 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← h3364 X3 X1 X3]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h3364 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3364 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l13 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l14 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3364 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l15 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h3364 sK0 X1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l16 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l15 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK2 (sK1 ◇ sK2)]
  have l18 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l16 sK0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h3364 (sK0 ◇ sK1) sK1 sK0]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l13 sK2 sK0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l22 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h3364 (sK0 ◇ sK1) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK2 X0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 sK1 sK2 sK2]
  have l25 : ∀ sK0 sK1 X1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 X1 X0 sK2
    conv => enter [1]; rw [h3364 (sK0 ◇ sK1) X1 X0]
    conv => enter [1, 2, 2]; rw [l22 sK0 sK1 X0 sK2]
  have l26 : ∀ sK0 sK1 X0 X1 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l27 : ∀ sK2 sK0 sK1 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 X1 sK2 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK2]
  have l29 : ∀ X1 sK2 sK0 sK1 X0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 sK2 sK0 sK1 X0
    conv => enter [1]; rw [h3364 X1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l27 sK2 sK0 sK1 (X0 ◇ (X1 ◇ X0))]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l27 sK2 sK0 sK1 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h3364 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK0 sK1 sK2 (sK1 ◇ sK2) sK2]
  have l32 : ∀ X1 sK2 sK0 sK1 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X1 sK2 sK0 sK1
    conv => enter [1]; rw [l29 X1 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← h3364 X1 (sK0 ◇ sK1) X1]
  have l33 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l31 sK1 sK2 sK0]
  have l34 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l32 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l33 sK2 sK0 sK1]
  have l35 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l36 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l35 sK1 sK0 sK2]
    conv => enter [1]; rw [l28 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l37 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l36 sK1 sK0 sK2]
  have l38 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l37 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l39 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h3364 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l40 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l41 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l38 sK1 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l40 sK1 sK2 sK0]
  have l42 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l22 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [l41 sK1 sK0 sK2]
  have l43 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l42 sK1 sK0 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [l43 sK1 sK0 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l22 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l32 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l46 sK0 sK2 sK1]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l47 sK0 sK1 sK2]
  have l49 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK2 X0]
    conv => enter [1, 1]; rw [← l47 sK0 sK1 sK2]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l49 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l51 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l48 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l50 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK2 X0]
  have l53 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l28 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l51 sK1 sK0 sK2]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK1]
    conv => enter [1]; rw [← l54 sK1 sK2 sK0]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2 sK2 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1 sK0 sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l53 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l59 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4287 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4287 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4315 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4315 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4339 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4339 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4340 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4340 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4286 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4286 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4318 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4318 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4271_implies_Equation4358 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4358 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4288 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4288 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4269 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4271 x y x]

@[equational_result]
theorem Equation4271_implies_Equation4270 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4271 x y y]

@[equational_result]
theorem Equation4271_implies_Equation4268 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4268 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4271 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4271_implies_Equation4314 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4314 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation4271_implies_Equation4283 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4283 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation4271_implies_Equation4284 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4284 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation4278_implies_Equation4287 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4287 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

@[equational_result]
theorem Equation4278_implies_Equation4300 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4300 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4278_implies_Equation4330 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4330 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4278 sK0 X0 sK1]
    conv => enter [1]; rw [h4278 sK0 X1 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4278_implies_Equation4340 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4340 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4296 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4296 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y y z]

@[equational_result]
theorem Equation4278_implies_Equation4327 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4327 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK2 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x x y]

@[equational_result]
theorem Equation4278_implies_Equation4362 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4362 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4278 sK2 X0 sK1]
    conv => enter [1]; rw [h4278 sK2 X1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4278 sK2 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z y x]

@[equational_result]
theorem Equation4278_implies_Equation4304 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4304 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK2 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4278 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4278_implies_Equation4269 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4278 x x y]

@[equational_result]
theorem Equation4278_implies_Equation4275 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [h4278 x y y]

@[equational_result]
theorem Equation4278_implies_Equation4272 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4278 x y x]

@[equational_result]
theorem Equation4278_implies_Equation4291 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4291 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y y]

@[equational_result]
theorem Equation4278_implies_Equation4320 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4320 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

@[equational_result]
theorem Equation4278_implies_Equation4284 (G : Type*) [Magma G] (h4278 : Equation4278 G) : Equation4284 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK1]
    conv => enter [1]; rw [h4278 sK1 X1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

@[equational_result]
theorem Equation4274_implies_Equation4295 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4295 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 y z x x y]

@[equational_result]
theorem Equation4274_implies_Equation4303 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4303 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 z y x x y]

@[equational_result]
theorem Equation4274_implies_Equation4344 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4344 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x y]

@[equational_result]
theorem Equation4274_implies_Equation4345 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4345 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 y z x x y]

@[equational_result]
theorem Equation4274_implies_Equation4271 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 x y z x]

@[equational_result]
theorem Equation4274_implies_Equation4278 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4278 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x x]

@[equational_result]
theorem Equation4274_implies_Equation4364 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4364 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK0 sK1 sK2 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK0]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z y z x]

@[equational_result]
theorem Equation4274_implies_Equation4301 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4301 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4274 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z z]

@[equational_result]
theorem Equation4274_implies_Equation4331 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4331 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4305 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4305 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 z y z x y]

@[equational_result]
theorem Equation4274_implies_Equation4325 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4325 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y x y z]

@[equational_result]
theorem Equation4274_implies_Equation4369 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z z x]

@[equational_result]
theorem Equation4274_implies_Equation4279 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z y x]

@[equational_result]
theorem Equation4274_implies_Equation4273 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [h4274 x y y]

@[equational_result]
theorem Equation4274_implies_Equation4299 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4299 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK2 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x x y]

@[equational_result]
theorem Equation4274_implies_Equation4297 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4297 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x x y y z]

@[equational_result]
theorem Equation4274_implies_Equation4277 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y y z x]

@[equational_result]
theorem Equation4274_implies_Equation4280 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation4274_implies_Equation4293 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4293 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x x y y x]

@[equational_result]
theorem Equation4274_implies_Equation4321 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4321 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 sK0 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y x y x]

@[equational_result]
theorem Equation4274_implies_Equation4343 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4343 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4274 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4274 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK0) sK0 sK1]
  have l5 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [h4274 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 X0 sK0 X1 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK0 sK1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y y]

@[equational_result]
theorem Equation4274_implies_Equation4290 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4290 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

@[equational_result]
theorem Equation4274_implies_Equation4276 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation4276 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4274 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4274 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4275 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4275 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4268 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4268 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4277 X1 X1 X2]
    conv => enter [1]; rw [h4277 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4277_implies_Equation4293 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4293 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4277 sK0 sK0 sK1]
    conv => enter [1]; rw [h4277 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4277_implies_Equation4276 (G : Type*) [Magma G] (h4277 : Equation4277 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4277 x y y]

@[equational_result]
theorem Equation4280_implies_Equation4270 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4280 x x y]

@[equational_result]
theorem Equation4280_implies_Equation4272 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4280 x y x]

@[equational_result]
theorem Equation4280_implies_Equation4343 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4343 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y y]

@[equational_result]
theorem Equation4280_implies_Equation4276 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4280 x y y]

@[equational_result]
theorem Equation4279_implies_Equation4273 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4273 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4279_implies_Equation4269 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4269 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4279_implies_Equation4321 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4279_implies_Equation4276 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h4279 x y y]

@[equational_result]
theorem Equation4286_implies_Equation4269 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4286 sK0 sK0 sK1]
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4286_implies_Equation4268 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4268 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4286 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4286_implies_Equation4283 (G : Type*) [Magma G] (h4286 : Equation4286 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4286 sK0 sK0 sK1]
    conv => enter [1]; rw [h4286 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4286 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4327_implies_Equation4269 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4327 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4327_implies_Equation4272 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4327 x x y]

@[equational_result]
theorem Equation4327_implies_Equation4320 (G : Type*) [Magma G] (h4327 : Equation4327 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h4327 x y y]

@[equational_result]
theorem Equation4287_implies_Equation4340 (G : Type*) [Magma G] (h4287 : Equation4287 G) : Equation4340 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← h4287 X0 sK1 sK2]
    conv => enter [1]; rw [h4287 X0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x z y]

@[equational_result]
theorem Equation4287_implies_Equation4269 (G : Type*) [Magma G] (h4287 : Equation4287 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4287 x x y]

@[equational_result]
theorem Equation4287_implies_Equation4284 (G : Type*) [Magma G] (h4287 : Equation4287 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4287 x y y]

@[equational_result]
theorem Equation4340_implies_Equation4287 (G : Type*) [Magma G] (h4340 : Equation4340 G) : Equation4287 G := by
  have l0 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h4340 X0 sK1 sK2]
    conv => enter [1]; rw [h4340 X0 sK1 X1]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4288_implies_Equation4270 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4288 x x y]

@[equational_result]
theorem Equation4288_implies_Equation4268 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h4288 x y x]

@[equational_result]
theorem Equation4288_implies_Equation4284 (G : Type*) [Magma G] (h4288 : Equation4288 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4288 x y y]

@[equational_result]
theorem Equation4304_implies_Equation4275 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4275 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4304 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4304_implies_Equation4272 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4304 x x y]

@[equational_result]
theorem Equation4304_implies_Equation4284 (G : Type*) [Magma G] (h4304 : Equation4304 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [h4304 x y x]

theorem Equation4295_4512_implies_Equation4345 (G : Type*) [Magma G] (h4295 : Equation4295 G) (h4512 : Equation4512 G) : Equation4345 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4295 X2 X0 X1]
    conv => enter [1]; rw [h4295 X2 X0 X0]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4295 (sK1 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [h4295 (sK1 ◇ sK1) X0 X1]
  have l2 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4295 (sK2 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [h4295 (sK2 ◇ sK0) X0 X1]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4295 sK1 (X0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4295 sK1 sK1 X0]
  have l4 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l4 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
  have l7 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h4295 (sK1 ◇ sK1) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4295 sK1 (sK2 ◇ sK0) sK1]
  have l8 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4295 (sK1 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [l7 sK1 X0 sK2 sK0]
  have l9 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l6 X0 sK0 sK1]
    conv => enter [1]; rw [← l6 X1 sK0 sK1]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 sK0 sK1]
    conv => enter [1]; rw [h4295 sK0 (sK1 ◇ sK1) sK2]
  have l11 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h4295 (sK2 ◇ sK0) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK1 sK0 sK2]
  have l12 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4295 (sK2 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [l11 sK2 sK0 X0 sK1]
  have l13 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l1 X0 sK0 sK1 X0]
    conv => enter [1]; rw [h4295 X0 (sK1 ◇ sK1) X1]
  have l14 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1 X0]
    conv => enter [1]; rw [h4295 sK0 (X0 ◇ (sK1 ◇ sK1)) sK2]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [h4295 sK1 (sK1 ◇ sK1) sK1]
  have l16 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [h4295 sK1 (X0 ◇ (sK1 ◇ sK1)) sK1]
  have l17 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4295 (sK2 ◇ sK0) (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 (sK2 ◇ sK0) (sK2 ◇ sK0) sK1 sK0]
  have l18 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l6 (sK2 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l20 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l14 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (sK2 ◇ sK0)]
  have l21 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK1 sK0 X0]
  have l22 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l2 X0 sK1 sK2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l20 sK0 sK1 X0 sK2]
  have l23 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l21 X0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1 sK2 sK0]
  have l24 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l22 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4295 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l25 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l15 sK1 sK0]
  have l26 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l25 X0 sK0 sK1]
    conv => enter [1]; rw [← l12 X0 sK1 sK2 sK0]
  have l27 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l18 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4295 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK1 ◇ sK1)]
  have l28 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l12 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l27 X0 sK1 sK0 sK2]
  have l29 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1, 2]; rw [← l23 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4295 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l30 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l23 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4295 (sK1 ◇ (sK2 ◇ sK0)) X1 sK1]
  have l31 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 X1 sK1 sK2 sK0]
  have l32 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l8 X0 sK0 sK1 X0]
    conv => enter [1]; rw [l29 X0 sK1 X0 sK0 X1]
  have l33 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l26 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l31 X1 X0 sK0 sK1 sK2]
  have l34 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l26 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 X0 sK0 sK1 X1]
  have l35 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l24 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 X1 sK1 sK2 sK0]
  have l36 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [← l24 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4295 X0 (sK1 ◇ (sK2 ◇ sK0)) X1]
  have l37 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l2 X0 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l36 X0 sK0 sK1 sK2 X1]
  have l38 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l26 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 X0 sK0 sK1 X1]
  have l39 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4295 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [l35 sK0 sK1 sK2 sK0 X0]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l33 sK0 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l39 sK1 sK2 sK0 sK0]
  have l41 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l38 X0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l24 X0 sK1 sK2 sK0]
  have l42 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 1]; rw [l6 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l43 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l40 sK0 sK1 sK2]
  have l44 : ∀ X0 sK0 sK1 X1 sK2 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 sK1 X1 sK2
    conv => enter [1, 1]; rw [l41 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK2 ◇ sK0) X1]
  have l45 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l34 X1 sK1 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l44 X0 sK0 sK1 X1 sK2]
  have l46 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l43 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l47 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l42 X0 sK0 sK1 X1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l48 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l45 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [← l46 sK1 sK2 sK0 X0]
  have l50 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [← h4295 sK1 X1 sK1]
    conv => enter [1]; rw [← l47 X0 sK0 sK1 X1]
  have l51 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l37 X0 sK1 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l49 sK0 X0 sK1 sK2]
  have l52 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [l50 X1 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l53 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4295 sK0 X0 sK2]
  have l54 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l52 X1 sK1 X1 sK0]
    conv => enter [1]; rw [← l48 X1 sK1 sK2 sK0 X1]
  have l55 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l54 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [l53 X1 sK1 sK2 sK0]
  have l56 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l7 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l33 X0 sK1 sK1 sK2 sK0]
  have l57 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l56 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l53 X0 sK1 sK2 sK0]
  have l58 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l57 sK1 X0 sK2 sK0]
  have l59 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l58 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 X0 sK0 sK1]
  have l60 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l59 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l58 X0 sK0 sK1 sK2]
  have l61 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l60 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l61 y z x]

@[equational_result]
theorem Equation4295_implies_Equation4287 (G : Type*) [Magma G] (h4295 : Equation4295 G) : Equation4287 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4295 sK1 X0 sK0]
    conv => enter [1]; rw [h4295 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4295_implies_Equation4369 (G : Type*) [Magma G] (h4295 : Equation4295 G) : Equation4369 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4295 sK2 X0 sK1]
    conv => enter [1]; rw [h4295 sK2 X0 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4295 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4295_implies_Equation4293 (G : Type*) [Magma G] (h4295 : Equation4295 G) : Equation4293 G := by
  intro x y
  conv => enter [1]; rw [h4295 x y y]

@[equational_result]
theorem Equation4295_implies_Equation4343 (G : Type*) [Magma G] (h4295 : Equation4295 G) : Equation4343 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4295 sK1 X0 sK1]
    conv => enter [1]; rw [h4295 sK1 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4295 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4295_implies_Equation4290 (G : Type*) [Magma G] (h4295 : Equation4295 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h4295 x y x]

@[equational_result]
theorem Equation4345_implies_Equation4295 (G : Type*) [Magma G] (h4345 : Equation4345 G) : Equation4295 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4345 sK1 X0 sK0]
    conv => enter [1]; rw [h4345 sK1 X0 X1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4345 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation4296_implies_Equation4269 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h4296 sK0 sK0 sK1]
    conv => enter [1]; rw [h4296 sK0 sK0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4296_implies_Equation4275 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h4296 y x x]

@[equational_result]
theorem Equation4296_implies_Equation4291 (G : Type*) [Magma G] (h4296 : Equation4296 G) : Equation4291 G := by
  intro x y
  conv => enter [1]; rw [h4296 x y x]

@[equational_result]
theorem Equation4318_implies_Equation4269 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4318 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4318_implies_Equation4270 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4318 x x y]

@[equational_result]
theorem Equation4318_implies_Equation4314 (G : Type*) [Magma G] (h4318 : Equation4318 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [h4318 x y y]

@[equational_result]
theorem Equation4297_implies_Equation4270 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4297 x x y]

@[equational_result]
theorem Equation4297_implies_Equation4275 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h4297 y x x]

@[equational_result]
theorem Equation4297_implies_Equation4290 (G : Type*) [Magma G] (h4297 : Equation4297 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h4297 x y x]

theorem Equation4299_4512_implies_Equation4297 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4297 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4299 sK2 sK2 X0]
    conv => enter [1]; rw [h4299 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 X0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l4 X1 sK0 sK1 sK0]
  have l6 : ∀ X2 X1 X0 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 X0 sK2
    conv => enter [1]; rw [← h4299 X1 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l7 : ∀ X2 X1 sK1 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 sK1 sK2
    conv => enter [1]; rw [l6 X2 X1 X2 sK2]
    conv => enter [1, 2]; rw [l0 X2 sK2 sK1]
  have l8 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l3 X1 X1 sK0 sK1]
    conv => enter [1]; rw [l7 X1 X1 sK1 sK2]
  have l9 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X1]
    conv => enter [1]; rw [l8 X1 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l7 X1 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y y z]

theorem Equation4299_4512_implies_Equation4288 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4288 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4299 sK2 sK2 X0]
    conv => enter [1]; rw [h4299 sK2 sK2 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 X0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l4 X1 sK0 sK1 sK0]
  have l6 : ∀ X2 X1 X0 sK2 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X2 X1 X0 sK2
    conv => enter [1]; rw [← h4299 X1 (sK2 ◇ sK2) X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 X0]
  have l7 : ∀ X1 sK0 sK1 X0 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l3 X1 X1 sK0 sK1]
    conv => enter [1]; rw [l6 X1 X1 X0 sK2]
  have l8 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l7 X1 sK0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [l0 X1 sK2 sK0]
  have l9 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X1]
    conv => enter [1]; rw [l8 X1 sK0 sK1 sK2]
  have l10 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← h4299 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK0]
  have l11 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l10 X1 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y x z]

theorem Equation4299_4512_implies_Equation4304 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4304 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4299 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4299 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK1 (sK0 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK0]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4299 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4299_4512_implies_Equation4277 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4277 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h4299 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4299 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4299 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4299 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK1 sK2 (sK1 ◇ sK1)]
  have l3 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← h4299 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← h4299 sK1 sK2 X0]
  have l4 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l0 X0 X0 sK0]
    conv => enter [1]; rw [l3 X0 X0 sK1 sK2]
  have l5 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l6 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l5 X1 sK1 sK2 sK1]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4299 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 X0 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4299_implies_Equation4280 (G : Type*) [Magma G] (h4299 : Equation4299 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4299 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4299 sK2 sK2 sK1]
    conv => enter [1]; rw [h4299 sK2 sK2 X0]
  have l2 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h4299 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4299 sK0 sK0 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l0 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 X0 X2]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h4299 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0 X0]
  have l7 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l5 X1 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation4300_implies_Equation4330 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4330 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4300 sK1 sK0 sK2]
    conv => enter [1]; rw [h4300 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4300_implies_Equation4272 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [h4300 x x y]

@[equational_result]
theorem Equation4300_implies_Equation4291 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4291 G := by
  intro x y
  conv => enter [1]; rw [h4300 x y y]

@[equational_result]
theorem Equation4339_implies_Equation4315 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4315 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4339 X0 sK1 sK2]
    conv => enter [1]; rw [h4339 X0 sK1 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4339_implies_Equation4268 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [h4339 x x y]

@[equational_result]
theorem Equation4339_implies_Equation4314 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [← h4339 x y x]

@[equational_result]
theorem Equation4301_implies_Equation4305 (G : Type*) [Magma G] (h4301 : Equation4301 G) : Equation4305 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4301 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4301 sK1 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4301 sK1 sK2 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4301 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4301_4512_implies_Equation4286 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4301 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 X0]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4301 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4301 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 X0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4301 sK0 sK1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l13 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4301 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X0]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l13 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l16 : ∀ X2 X0 sK0 sK1 : G, (X2 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X2 X0 sK0 sK1
    conv => enter [1]; rw [← h4301 X0 X2 X2]
    conv => enter [1]; rw [l15 X0 X2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l16 x z x y]

end Semigroup4
