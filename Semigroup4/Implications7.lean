import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

theorem Equation4269_4343_4512_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4269 X0 X1]
    conv => enter [1]; rw [h4269 X0 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4269 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [h4343 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4343 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4343 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l12 X0 sK0]
  have l14 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h4269 X0 X1]
  have l15 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l13 sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l14 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l18 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l19 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l17 X1 X0 X2]
    conv => enter [1, 2]; rw [← l2 X0 X0 X0]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l18 X0 X1 sK0]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l19 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0]
    conv => enter [1]; rw [← l21 X0 X0 sK0]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4269_4293_4512_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4269 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4293 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4293 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ X1)]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [h4293 (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l15 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l21 sK0 X0]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l23 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l24 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l22 sK0 X0]
  have l26 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l23 sK1 sK2 sK1]
    conv => enter [1]; rw [← l25 sK1 sK2 X0 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l26 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation4269_4321_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4321 : Equation4321 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4321 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4269_4320_implies_Equation4327 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4320 : Equation4320 G) : Equation4327 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4320 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4269_4283_implies_Equation4286 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4283 : Equation4283 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4269 sK0 sK2]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4283 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation4269_4314_implies_Equation4318 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4314 : Equation4314 G) : Equation4318 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [h4314 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4269_4291_implies_Equation4296 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4291 : Equation4291 G) : Equation4296 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4291 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4269_4290_4512_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4290 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [l4 X0 sK0 X1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4290 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l15 X0 sK0]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l18 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4269_4276_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4276 : Equation4276 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 X1]
    conv => enter [1]; rw [h4269 X1 X2]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4276 X0 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  have l3 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← l1 X1 X1 X2]
    conv => enter [1]; rw [l2 X1 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4269_4275_implies_Equation4296 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4275 : Equation4275 G) : Equation4296 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [h4275 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4269_4270_implies_Equation4318 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4270 : Equation4270 G) : Equation4318 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4270 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4269_4273_implies_Equation4279 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4273 : Equation4273 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4273 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4279_4287_4512_implies_Equation4274 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4287 : Equation4287 G) (h4512 : Equation4512 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4279 sK0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK0 X1 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4279 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4279 sK0 (sK0 ◇ sK2) sK1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK0 sK0]
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2]; rw [h4279 sK0 X2 X1]
    conv => enter [1]; rw [← h4287 X0 (X1 ◇ X2) X2]
  have l5 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l4 X0 sK0 X1 X2]
  have l6 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4287 X0 sK2 sK0]
    conv => enter [1]; rw [h4287 X0 sK2 X1]
  have l7 : ∀ sK0 X0 X3 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X3 X1 X2
    conv => enter [1]; rw [l5 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4287 X0 (X1 ◇ X2) X3]
  have l8 : ∀ X2 sK0 sK2 X0 X1 : G, (X2 ◇ (sK0 ◇ sK2)) = (X2 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro X2 sK0 sK2 X0 X1
    conv => enter [1]; rw [l6 X2 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK0 X2 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l7 sK0 X2 sK0 sK0 sK2]
    conv => enter [1]; rw [← l8 X2 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4269_4272_implies_Equation4327 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4272 : Equation4272 G) : Equation4327 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4272 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4268_4269_implies_Equation4286 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4269 : Equation4269 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4268 sK0 sK1]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4269 sK0 sK2]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4296_4300_implies_Equation4278 (G : Type*) [Magma G] (h4296 : Equation4296 G) (h4300 : Equation4300 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4296 sK2 sK0 sK0]
    conv => enter [1]; rw [h4300 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4286_4288_4315_implies_Equation4271 (G : Type*) [Magma G] (h4286 : Equation4286 G) (h4288 : Equation4288 G) (h4315 : Equation4315 G) : Equation4271 G := by
  have l0 : ∀ X0 X2 sK0 : G, (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [← h4286 X0 X0 X2]
    conv => enter [1]; rw [h4288 X0 X0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h4315 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 sK0]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l1 X0 sK1 X0 sK0]
    conv => enter [1]; rw [h4315 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x x y z]

theorem Equation4287_4296_implies_Equation4278 (G : Type*) [Magma G] (h4287 : Equation4287 G) (h4296 : Equation4296 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4287 X0 sK0 sK0]
    conv => enter [1]; rw [h4287 X0 sK0 X1]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4287 X0 sK0 sK0]
    conv => enter [1]; rw [h4287 X0 sK0 sK2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4296 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l0 X0 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4286_4287_implies_Equation4271 (G : Type*) [Magma G] (h4286 : Equation4286 G) (h4287 : Equation4287 G) : Equation4271 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4286 sK0 X1 sK0]
    conv => enter [1]; rw [h4287 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4268_4272_implies_Equation4299 (G : Type*) [Magma G] (h4268 : Equation4268 G) (h4272 : Equation4272 G) : Equation4299 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4272 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation3253_4343_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4343 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation3253_4293_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4293 sK0 X0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4293 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation3253_4321_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4321 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation3253_4314_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4314 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation3253_4291_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4291 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3253 sK0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h3253 X0]
    conv => enter [1]; rw [h4291 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3253 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4291 X0 X1]
    conv => enter [1]; rw [h4291 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4291 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4291 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← l3 X0 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1]; rw [← l7 X0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [← h4291 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l11 sK0]
  intro x
  conv => enter [1]; rw [l12 x]

theorem Equation3253_4284_4512_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4284 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l3 sK0]
  intro x
  conv => enter [1]; rw [l4 x]

theorem Equation3253_4276_4512_implies_Equation316 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4276 X0 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4276 sK1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK1]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3253_4276_4512_implies_Equation3294 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) : Equation3294 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4276 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 X0 sK0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l10 X0 sK0]
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2, 2]; rw [l10 X0 sK0]
  have l14 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l14 X0 X1 sK0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l16 X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation3253_4275_4512_implies_Equation3271 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4275 : Equation4275 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4275 X1 X0]
    conv => enter [1]; rw [h4275 X1 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h3253 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h4275 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4275 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h3253 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h4275 (sK1 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h4275 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ X0)]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [← l5 X0 sK0]
    conv => enter [1]; rw [l12 sK0 X0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ sK0) sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h4275 X0 X1]
    conv => enter [1]; rw [l5 X0 sK0]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4275 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK0) X0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l21 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l22 sK1 sK0 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4275 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l30 x y]

theorem Equation3253_4275_implies_Equation3261 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4275 : Equation4275 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4275 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3253_4275_implies_Equation3278 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4275 : Equation4275 G) : Equation3278 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [← h4275 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4275 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4275 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3253_4270_4512_implies_Equation3259 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation3259 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l0 X0 X1 sK0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4270 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0 sK0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l3 X0 X1 sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l4 X0 X1 X2 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4270 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [l6 X0 X1 X1 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h3253 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation3253_4270_implies_Equation3256 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4270 : Equation4270 G) : Equation3256 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4270 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3253_4270_4512_implies_Equation3261 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) : Equation3261 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4270 X0 X1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4270 X0 sK0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h3253 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h3253 sK0]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4270 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 X0]
    conv => enter [1, 2]; rw [l1 X1 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l7 X0 X1 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l9 X0 X1 X2 sK0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l11 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4270 X1 (X0 ◇ X1)]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1]; rw [l13 X0 X1 X1 sK0]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l13 X0 X0 (X0 ◇ X1) sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4270 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l25 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4270 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l17 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l32 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4270 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l41 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l40 sK0 X0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l45 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l44 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l46 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l45 sK0 X0 sK1]
    conv => enter [1]; rw [← l41 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) sK1]
  have l47 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l46 sK0 X0 sK1]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l43 sK0 sK1]
  have l49 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l52 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l47 sK0 X0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1 X0]
  have l53 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l52 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [l51 sK1 sK0]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1]; rw [l62 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l61 sK1 sK0]
  have l66 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l65 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l70 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [l17 X0 X0 sK0]
  have l71 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l20 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l71 sK1 sK0]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [l66 sK1 sK0 (sK1 ◇ sK0)]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l70 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l73 sK1 sK0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← l74 sK1 sK0]
  have l76 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l77 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l76 sK1 X0 sK0]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4270 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l22 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l78 sK1 sK0]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l77 sK1 (sK1 ◇ sK0) sK0]
  have l81 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l80 sK1 sK0]
  have l82 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l17 X0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l81 sK1 sK0]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l81 sK1 sK0]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0 sK0]
    conv => enter [1]; rw [l82 sK1 sK0 sK1]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l83 sK1 sK0]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l85 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [← l86 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l87 x y]

theorem Equation3253_4273_4512_implies_Equation40 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4273 sK1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK1) sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3253 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l9 sK1]
    conv => enter [1]; rw [h4273 (sK1 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [l10 sK1 X0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3253_4273_4512_implies_Equation3269 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation3269 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3253_4273_4512_implies_Equation3282 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation3282 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4273 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3253 sK0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4273 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3253 sK1]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h4273 X0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← h4273 sK1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4273 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4273 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h4273 sK1 X0]
  have l8 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l9 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l7 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l11 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l9 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l11 sK1 X0 sK0]
    conv => enter [1]; rw [← l10 sK1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l18 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4273 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation3253_4273_4512_implies_Equation3294 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation3294 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [h4273 sK1 X0]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [← h3253 sK1]
  have l2 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4273 sK0 sK1]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4273 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4273 sK2 X0]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← h4273 X0 X1]
  have l8 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X0 sK1 sK2]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h3253 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l3 sK2 sK1 sK0]
  have l11 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← h4273 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK2]
  have l13 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l11 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l14 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [← l10 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1) = (X0 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← l8 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK1 X0]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ X0) sK2]
  have l19 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l14 sK2 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l17 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l22 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l19 sK2 sK1 X0 sK0]
    conv => enter [1]; rw [← l16 sK2 sK1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l21 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l24 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ sK2))]
  have l29 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 sK2]
  have l30 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l29 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l31 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l31 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) X0]
  have l33 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l32 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l22 sK2 sK1 X0 sK0]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))))]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 (sK2 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK2]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← l18 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l38 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [h4273 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l39 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l38 sK2 sK1 X0]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l39 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1]; rw [← l33 sK2 sK1 sK0 sK0]
  have l42 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l39 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l41 sK0 sK2 sK1]
  have l43 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l42 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ (sK1 ◇ sK2))]
  have l44 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l43 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4273 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ sK2))]
  have l45 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l44 sK2 sK1 sK0]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l45 sK0 sK2 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l46 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

theorem Equation3253_4273_4512_implies_Equation3297 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4273 : Equation4273 G) (h4512 : Equation4512 G) : Equation3297 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4273 X1 X0]
    conv => enter [1]; rw [h4273 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4273 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4273 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4273 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4273 sK2 X0]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3253 sK2]
    conv => enter [1, 2]; rw [h4273 sK2 (sK2 ◇ sK1)]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h3253 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
  have l7 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l2 sK2 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
  have l10 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l7 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
  have l11 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l6 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l10 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
  have l14 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l11 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l13 sK2 X0 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
  have l17 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l14 sK2 X0 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l18 sK0]
    conv => enter [1]; rw [h4273 (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l23 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 sK2]
  have l24 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK2 sK1 X0]
    conv => enter [1]; rw [l21 sK2 sK1 X0]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l26 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4273 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l25 sK2 sK1]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK2 sK1 sK1]
    conv => enter [1]; rw [l26 sK2 sK1]
  have l28 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l28 sK1 sK2 X0]
  have l30 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK2 sK1 (sK0 ◇ sK0)]
  have l31 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l23 sK2 sK1]
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l23 sK2 sK1]
  have l32 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l27 sK1 sK2]
  have l33 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) sK1]
  have l34 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4273 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l32 X0 sK2 sK1]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK1 sK2]
    conv => enter [1]; rw [l33 sK1 sK2 sK1]
  have l36 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4273 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l35 sK1 sK2]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l36 sK2 sK1]
    conv => enter [1]; rw [l23 sK2 sK1]
  have l38 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = (((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l33 ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2 sK1]
    conv => enter [1, 2]; rw [l33 (sK2 ◇ (sK2 ◇ sK1)) sK2 sK1]
  have l39 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l33 (sK0 ◇ sK0) sK2 sK1]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l39 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK0) ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l41 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1)) ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l42 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [l37 sK1 sK2]
  have l43 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l41 sK1 sK2]
    conv => enter [1]; rw [l17 sK2 sK1 ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1)]
  have l44 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l42 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l31 sK2 sK1 sK0]
  have l45 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1, 2]; rw [← l24 sK1 sK2 sK1]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK2 sK1]
    conv => enter [1]; rw [← l29 sK1 sK2 sK2]
  have l47 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
  have l48 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l16 sK2 sK1 sK1]
    conv => enter [1]; rw [← l47 sK1 sK2]
  have l49 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l48 sK2 sK1]
    conv => enter [1]; rw [l37 sK1 sK2]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l49 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l50 x y z]

theorem Equation3253_4272_4512_implies_Equation312 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4272 : Equation4272 G) (h4512 : Equation4512 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4272 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4272 sK0 sK1]
    conv => enter [1]; rw [h4272 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4272 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4272 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l6 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3253_4268_implies_Equation308 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4268 : Equation4268 G) : Equation308 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1]; rw [← h4268 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h4268 X0 X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [h4268 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3253_4269_4512_implies_Equation309 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation309 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4269 sK0 sK1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4269 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4269 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4269 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3253_4269_4512_implies_Equation3264 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation3264 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0]
  have l8 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK2]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l10 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l9 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation3253_4269_4512_implies_Equation4284 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation4284 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4269 X0 X1]
    conv => enter [1]; rw [h4269 X0 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1, 2]; rw [h4269 X0 X1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3253 sK1]
    conv => enter [1, 2]; rw [h4269 sK1 sK0]
  have l3 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4269 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4269 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l6 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4269 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 X0 X1]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l7 X0 X2 X1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l9 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4269 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [h4269 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4269 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4269 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4269 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3253 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ sK1)]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l22 : ∀ X2 X0 X1 : G, ((X2 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 (X2 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X2 X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h4269 X0 X1]
  have l24 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l26 : ∀ X2 X0 X1 : G, ((X2 ◇ X0) ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l22 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 X0 ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1, 2]; rw [l11 X0 (X1 ◇ X0) (X0 ◇ X0)]
  have l29 : ∀ X2 X0 X1 : G, ((X2 ◇ X0) ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l26 X2 X0 X1]
    conv => enter [1, 2]; rw [l11 X0 (X2 ◇ X0) (X1 ◇ X0)]
  have l30 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 X0 X0 X0]
  have l32 : ∀ X2 X0 : G, (X2 ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := by
    intro X2 X0
    conv => enter [1, 2]; rw [l24 X0 X0 X2]
    conv => enter [1]; rw [← l29 X2 X0 X2]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l4 X0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← l30 X0 X1]
  have l34 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2]; rw [← l4 X0 X0 X0]
  have l35 : ∀ X2 X0 : G, (X2 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X2 X0
    conv => enter [1]; rw [l32 X2 X0]
    conv => enter [1]; rw [← h4512 X2 X0 (X2 ◇ X0)]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l34 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l36 X0 X1]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1]; rw [← l35 X1 X0]
  have l40 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X0 X1]
    conv => enter [1]; rw [l38 X0 X1]
  have l41 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1, 2]; rw [l39 X1 X0]
  have l42 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l41 X0 X0]
    conv => enter [1]; rw [← l4 X0 X0 X0]
  have l43 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0]
    conv => enter [1]; rw [l0 X0 X0 X1]
  have l44 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ (X0 ◇ sK1)) = ((X0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l43 (X0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 X0]
  have l45 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l43 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l46 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l45 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l47 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l44 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l48 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l46 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l49 : ∀ X0 sK1 : G, ((X0 ◇ sK1) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l47 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l17 sK1 X0]
  have l50 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l49 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK1 (X0 ◇ sK1)]
  have l51 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l50 X0 sK1]
    conv => enter [1]; rw [l48 X0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [← l51 x y]

theorem Equation3355_4512_implies_Equation3342 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3342 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [l2 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [l3 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [l6 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l10 : ∀ sK0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3355 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l9 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h3355 sK1 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 (sK0 ◇ sK0)]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l19 sK0 (X0 ◇ X1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l22 sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l27 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 (sK0 ◇ sK1)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l36 x y]

theorem Equation3355_4512_implies_Equation3308 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3308 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h3355 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [h3355 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h3355 sK1 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ sK1) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h3355 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3355 sK1 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← h3355 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l15 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l11 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)]
  have l17 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1]; rw [← h3355 (X0 ◇ X2) X1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [l11 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))]
  have l19 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X2 X1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h3355 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK1 ◇ X0) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h3355 (sK1 ◇ X0) sK0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [← l27 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l34 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l37 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l36 sK0 sK1 X0]
    conv => enter [1]; rw [← l35 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l35 sK0 sK1 X0]
    conv => enter [1]; rw [← l37 sK0 X0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1]; rw [l38 sK0 sK1 X0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3355 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h3355 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l42 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ sK1)]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h3355 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [l42 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1, 2]; rw [l30 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [l47 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l51 sK0 sK1]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l51 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1 (sK0 ◇ sK1)]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l54 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l42 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l62 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l30 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l63 sK1 sK0]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l65 sK1 sK0]
  have l67 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l66 sK1 sK0]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [l67 sK1 sK0]
  have l69 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [l60 sK0 sK1]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l69 sK1 sK0]
  have l71 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3355 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l72 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l19 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l73 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [← l19 X0 X2 X1]
    conv => enter [1]; rw [← h4512 (X0 ◇ X2) X1 X3]
  have l74 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l73 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l75 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l74 X0 X1 X2 X3]
  have l76 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l75 X0 X1 X2 X3]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l64 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l59 sK1 sK0]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l70 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l78 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [l76 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← l72 sK0 sK1 sK1]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l82 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l83 sK0 sK1]
    conv => enter [1]; rw [l78 sK0 sK1]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l84 sK0 sK1]
  have l86 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
  have l87 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l88 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0]
    conv => enter [1]; rw [← l87 sK1 sK0]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l88 sK1 sK0]
    conv => enter [1]; rw [← l71 sK0 sK1 sK1]
  have l91 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1]; rw [← l89 sK0 sK1]
  have l92 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l93 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l92 sK1 sK0 X0]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [← l91 sK1 sK0]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [← l93 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1]
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 sK1]
    conv => enter [1]; rw [← l97 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l98 x y]

theorem Equation3355_4512_implies_Equation3346 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3346 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h3355 sK1 sK1]
    conv => enter [1]; rw [← h3355 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [← h3355 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3355 sK1 sK1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK1 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h3355 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 sK1]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3355 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h3355 X0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l18 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h3355 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 (sK1 ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l28 sK0 sK1 X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l32 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [l38 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l48 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← l49 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← h3355 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK1 ◇ sK1))]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [l37 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l43 sK0 sK1]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1)]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1, 2]; rw [l63 sK1 sK0]
  have l65 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l63 sK1 sK0]
    conv => enter [1]; rw [h3355 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l63 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l65 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK1 ◇ sK1) sK0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l69 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l70 x y]

theorem Equation3355_4512_implies_Equation3315 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3315 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h3355 sK0 sK0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h3355 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK1) ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h3355 sK0 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← h3355 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l7 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h3355 (sK0 ◇ X0) sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK1)]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ sK1)]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l27 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l29 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK0)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l25 sK0 sK1 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ sK1)]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h3355 (sK0 ◇ sK0) sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK1)]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1)]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l57 sK1 sK0]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [← l43 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [l62 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l63 sK1 sK0]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l65 sK0 sK1]
  have l67 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l68 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l67 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l69 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l68 sK1 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 (sK1 ◇ (sK0 ◇ sK0))]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [l69 sK1 sK0 (sK0 ◇ sK1)]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1, 2]; rw [l69 sK1 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l73 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l74 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l75 x y]

theorem Equation3355_4512_implies_Equation3353 (G : Type*) [Magma G] (h3355 : Equation3355 G) (h4512 : Equation4512 G) : Equation3353 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h3355 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h3355 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← h3355 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← h3355 (X0 ◇ X2) X1]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK1 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X2 X1]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h3355 X0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← l15 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← h3355 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l24 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l24 sK1 sK0 X0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))]
    conv => enter [1, 2]; rw [← h3355 X0 (sK1 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l26 sK1 sK0 X0]
    conv => enter [1]; rw [← l25 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [← l27 sK1 X0 sK0]
  have l29 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK0 X0]
    conv => enter [1]; rw [l28 sK1 sK0 X0]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l30 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [l38 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l41 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l39 sK0 sK1]
  have l44 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← h3355 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ sK1))]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l44 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2]; rw [← l42 sK0 sK1]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0 sK0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l50 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l53 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [← l14 X0 X2 X1]
    conv => enter [1]; rw [← h4512 (X0 ◇ X2) X1 X3]
  have l54 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l53 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l55 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l54 X0 X1 X2 X3]
  have l56 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l55 X0 X1 X2 X3]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l52 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l56 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l47 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l38 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1, 2]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) X0]
  have l64 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l63 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l64 sK1 sK0 X0]
    conv => enter [1]; rw [← h3355 X0 (sK0 ◇ sK1)]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l65 sK1 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 sK0 sK1]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3355 sK1 sK0]
    conv => enter [1, 2]; rw [← l65 sK1 sK0 sK0]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 sK0]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1, 2]; rw [l52 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← l69 sK1 sK0]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3355 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l70 sK1 sK0]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← h3355 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [← l71 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l74 x y]

end Semigroup4
