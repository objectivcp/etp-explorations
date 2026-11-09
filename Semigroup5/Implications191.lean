import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4280_4512_implies_Equation54256 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54256 G := by
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
  have l6 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l0 X0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK0 sK1]
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
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l6 X0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_54256_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54256 : Equation54256 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54256 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54256 X0 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54256 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h54256 sK0 sK0 X0]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h54256 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54256 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54256 X0 X1 (X1 ◇ (X1 ◇ X0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

theorem Equation4280_4512_implies_Equation54258 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54258 G := by
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
  have l6 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l0 X0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK0 sK1]
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
    conv => enter [1]; rw [← h4280 sK1 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l6 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l13 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l13 x y z z]

theorem Equation4512_54258_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54258 : Equation54258 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54258 X0 sK2 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [h54258 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK1]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2]
  have l7 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK2]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l7 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK2 sK1]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54258 X0 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l10 sK1 sK2 sK0]
  have l12 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0]
  have l13 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [← l12 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x x y z]

theorem Equation4280_4512_implies_Equation54259 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54259 G := by
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
  have l6 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK1]
  have l7 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK1 sK2]
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
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [l10 sK2 sK1 X0]
  have l12 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l6 X0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK0]
  have l13 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK1 sK2 sK0 X0]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

@[equational_result]
theorem Equation54259_implies_Equation4280 (G : Type*) [Magma G] (h54259 : Equation54259 G) : Equation4280 G := by
  have l0 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54259 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [h54259 X2 sK0 X0 sK0]
  have l1 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l0 X1 X2 X3 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h54259 sK0 sK0 X1 sK0]
  have l2 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l1 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← h54259 sK0 sK0 X2 sK0]
  have l3 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l2 X1 X2 X1 sK0]
    conv => enter [1]; rw [← h54259 sK0 sK0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54267 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54267 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4280 sK2 sK2 sK0]
    conv => enter [1]; rw [h4280 sK2 X0 sK0]
  have l1 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h4280 sK2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK2]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4280 sK2 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 X0 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4280 sK2 sK1 sK2]
    conv => enter [1]; rw [h4280 sK2 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y w]
  conv => enter [1]; rw [l2 y w z]

theorem Equation4512_54267_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54267 : Equation54267 G) : Equation4280 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54267 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54267 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l1 (sK0 ◇ sK0) sK0 X0]
  have l3 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l2 X1 X2 X3 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK0 X1]
  have l4 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l3 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0 X2]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54286 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54286 G := by
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
  have l3 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y w x]
  conv => enter [1]; rw [l2 w x z]

theorem Equation4512_54286_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54286 : Equation54286 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54286 sK0 X0 X1 sK0]
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
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54286 X0 X1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

theorem Equation4280_4512_implies_Equation54301 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54301 G := by
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
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK1 X1]
  have l9 : ∀ sK1 sK2 X0 sK0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X1 X0]
  have l10 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4280 sK2 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 X0 sK2 sK2]
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
  conv => enter [1]; rw [l13 x y z w x]

theorem Equation4512_54301_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54301 : Equation54301 G) : Equation4280 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54301 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [h54301 sK0 sK0 X1 sK0]
  have l6 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 X1]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

theorem Equation4280_4512_implies_Equation54303 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54303 G := by
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
  have l7 : ∀ sK0 sK3 X1 X0 : G, ((sK0 ◇ sK3) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK3 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK3 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK3 X1]
  have l8 : ∀ sK1 sK2 X0 sK0 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK3) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 sK0 sK3 X1
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 sK3 X1 X0]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4280 sK2 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X0 sK2 sK2 sK2]
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
  conv => enter [1]; rw [l12 x y z w z]

theorem Equation4512_54303_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54303 : Equation54303 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54303 X0 X1 sK2 sK2]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54303 X0 X1 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK0]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 sK2]
  have l4 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l0 sK2 sK0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54304 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54304 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4280 sK0 (sK0 ◇ sK0) sK0]
  intro x y z w
  conv => enter [1]; rw [← h4280 w x y]
  conv => enter [1]; rw [l0 w z]

theorem Equation4512_54304_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54304 : Equation54304 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54304 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
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
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

theorem Equation4280_4512_implies_Equation54305 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54305 G := by
  have l0 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4280 sK3 sK2 sK3]
    conv => enter [1]; rw [h4280 sK3 X0 sK3]
  have l1 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [h4280 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK3 ◇ sK3) sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4280 sK3 sK2 sK3]
    conv => enter [1]; rw [l1 sK3 X0 sK2]
  have l3 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [← h4280 (sK2 ◇ (sK3 ◇ sK3)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK2 sK3 (sK2 ◇ (sK3 ◇ sK3))]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [← l3 X0 X1 sK2 sK3]
  have l5 : ∀ X0 X1 X2 sK2 sK3 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) := by
    intro X0 X1 X2 sK2 sK3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK2 sK3]
  have l6 : ∀ sK2 sK3 X2 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK2 sK3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ X1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK0 X1]
  have l8 : ∀ sK2 sK3 X0 sK1 sK0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) = ((sK1 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 sK1 sK0 X1
    conv => enter [1]; rw [l6 sK2 sK3 X0 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 sK0 X1 X0]
  have l9 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [h4280 sK3 (sK3 ◇ sK3) sK3]
    conv => enter [1]; rw [← l8 sK2 sK3 X0 sK3 sK3 sK3]
  have l10 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4280 sK3 sK2 sK3]
    conv => enter [1]; rw [l9 sK3 sK2 X0]
  have l11 : ∀ sK2 sK3 X2 X3 X4 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK2 sK3 X2 X3 X4
    conv => enter [1]; rw [l10 sK2 sK3 X4]
    conv => enter [1]; rw [← l5 X2 X3 X4 sK2 sK3]
  have l12 : ∀ sK2 sK3 X2 X3 X4 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK2 sK3 X2 X3 X4
    conv => enter [1]; rw [l11 sK2 sK3 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

theorem Equation4512_54305_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54305 : Equation54305 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54305 sK0 sK0 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54305 sK1 sK2 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54310 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54310 G := by
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
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4280 sK0 sK2 sK3]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l3 x y w u]
  conv => enter [1]; rw [l2 w u z]

theorem Equation4512_54310_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54310 : Equation54310 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54310 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
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
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54279 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4280 sK0 (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← h4280 z x y]
  conv => enter [1]; rw [l0 z z]

theorem Equation4512_54279_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54279 : Equation54279 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54279 X0 X1 sK2]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4280_4512_implies_Equation54277 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54277 G := by
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
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK1 X1]
  have l9 : ∀ sK1 sK2 X0 sK0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X1 X0]
  have l10 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4280 sK2 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 X0 sK2 sK2]
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
  intro x y z
  conv => enter [1]; rw [l13 x y z z x]

theorem Equation4512_54277_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation4280 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l9 : ∀ sK2 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h54277 X0 X1 sK2]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54277 X0 X1 sK0]
  have l11 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [← h54277 X0 X1 sK2]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54277 sK2 X0 sK2]
  have l14 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h54277 (sK2 ◇ sK2) sK1 sK1]
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ sK2) sK1]
  have l15 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l13 sK2 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2 sK2]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK1 sK2]
  have l17 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l16 sK2 sK1]
  have l18 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l17 sK2 sK1]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l18 sK2 sK1]
    conv => enter [1]; rw [← h54277 (sK1 ◇ (sK2 ◇ sK2)) X0 sK1]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l24 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK2 ◇ sK2)]
  have l25 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0) sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l30 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 (sK2 ◇ sK2) sK2]
  have l34 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l33 sK0 sK2]
  have l35 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l34 sK0 sK2]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l35 sK0 sK2]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l36 sK0 sK0]
  have l38 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [← l12 sK2 sK2 sK2]
    conv => enter [1]; rw [← l15 sK2 sK2]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [← l38 sK2]
  have l40 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1, 2]; rw [l39 sK2 sK0]
  have l41 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l12 sK1 sK1 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2 sK1]
  have l43 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54277 sK2 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l42 sK1 sK2]
  have l44 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l43 sK2 X0 sK1]
    conv => enter [1]; rw [← l11 sK2 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l45 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l44 sK2 X0 sK1]
    conv => enter [1]; rw [l7 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l46 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l45 sK2 X0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l46 sK2 sK1 sK1]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1]
  have l48 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l15 sK2 sK2]
    conv => enter [1]; rw [← l47 sK1 sK2 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK2]
    conv => enter [1]; rw [l48 sK2 sK1]
  have l50 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l12 sK1 sK1 sK2]
    conv => enter [1]; rw [← l24 sK1 sK2 sK1]
  have l51 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l51 y z x]

theorem Equation4280_4512_implies_Equation54213 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54213 G := by
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
  have l3 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [← h4280 (sK2 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l3 X0 X1 sK2 sK0]
  have l5 : ∀ X0 X1 X2 sK2 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK2 sK0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h4280 sK0 sK2 sK0]
  have l7 : ∀ sK2 sK0 X2 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK2 sK0 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK0 X1]
  have l10 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l7 sK2 sK0 X0 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 X1 X0]
  have l11 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l6 sK0 X0 sK2]
    conv => enter [1]; rw [l8 sK0 X0]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4280 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 sK2 sK0 X0 sK0]
  have l13 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 sK2 X0]
  have l14 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK0 sK1]
    conv => enter [1]; rw [l11 sK2 sK0 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l14 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l15 y z x]

theorem Equation4512_54213_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54213 : Equation54213 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54213 X0 sK2 sK2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54213 X0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK2 X1 X0 : G, (((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l3 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l3 sK2 X0 X1]
  have l5 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l2 sK2 X1 X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l0 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l8 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l6 X0 sK2 sK1]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h54213 sK1 (sK2 ◇ sK2) X0]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 ((sK2 ◇ sK2) ◇ X0)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 sK2 X0 (sK1 ◇ (sK2 ◇ sK2))]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) sK2 X0 sK1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l14 x x y z]

theorem Equation4280_4512_implies_Equation54280 (G : Type*) [Magma G] (h4280 : Equation4280 G) (h4512 : Equation4512 G) : Equation54280 G := by
  have l0 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK3]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK3]
  have l3 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [← h4280 (sK3 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l3 X0 X1 sK3 sK0]
  have l5 : ∀ X0 X1 X2 sK3 sK0 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK3 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 X0 X1 sK3 sK0]
  have l6 : ∀ sK3 sK0 X2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK3 sK0 X2 X0 X1
    conv => enter [1]; rw [← l5 X0 X1 X2 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4280 X0 sK0 X1]
  have l8 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l6 sK3 sK0 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X1 X0]
  have l9 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4280 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 X0 sK0]
  have l10 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [l9 sK0 sK3 X0]
  have l11 : ∀ sK3 sK0 X2 X3 X4 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X2 ◇ ((X3 ◇ X3) ◇ X4)) := by
    intro sK3 sK0 X2 X3 X4
    conv => enter [1]; rw [l10 sK3 sK0 X4]
    conv => enter [1]; rw [← l5 X2 X3 X4 sK3 sK0]
  have l12 : ∀ sK3 sK0 X2 X3 X4 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ (X3 ◇ X4))) := by
    intro sK3 sK0 X2 X3 X4
    conv => enter [1]; rw [l11 sK3 sK0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l12 x y z z w]

theorem Equation4512_54280_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54280 : Equation54280 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54280 X0 X1 sK2 sK2]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54269 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54269 G := by
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
  have l3 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4280 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z x]
  conv => enter [1]; rw [l2 z x z]

theorem Equation4512_54269_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54269 : Equation54269 G) : Equation4280 G := by
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
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54269 sK0 X0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54269 (sK0 ◇ sK0) X0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54269 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54269 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ X0)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0 sK2]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) (sK0 ◇ sK0) sK2]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [l13 sK0 sK2]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 sK2]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0 sK2]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l14 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) (sK0 ◇ sK0) sK2]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l20 sK0]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l24 sK0]
  have l26 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l25 sK0]
    conv => enter [1]; rw [l23 sK0 sK2]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l26 sK0 sK0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54269 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [← l27 sK0]
  intro x y z
  conv => enter [1]; rw [← l30 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54216 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54216 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y y z]
  conv => enter [1]; rw [l4 y z y]

theorem Equation4512_54216_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54216 : Equation54216 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54216 X0 sK0 sK0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← h54216 X0 sK2 sK2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l2 sK2 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l4 sK2 sK1]
    conv => enter [1]; rw [l4 sK2 X0]
  have l6 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54216 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l3 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l6 X0 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l9 x x y z]

@[equational_result]
theorem Equation4280_implies_Equation54284 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54284 G := by
  have l0 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [h4280 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h4280 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK3]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK0 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4280 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK3]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 X0]
    conv => enter [1, 2]; rw [l3 sK1 sK1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l4 z w z]

theorem Equation4512_54284_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54284 : Equation54284 G) : Equation4280 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54284 X0 X1 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

@[equational_result]
theorem Equation4280_implies_Equation54245 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54245 G := by
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
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x z z]

theorem Equation4512_54245_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54245 : Equation54245 G) : Equation4280 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54245 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h54245 sK0 X1 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 sK0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK2]
  have l9 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 sK2]
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l5 sK0 sK2]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54245 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [l5 sK0 sK2]
  have l12 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54245 X0 sK0 sK0]
    conv => enter [1]; rw [← h54245 X0 sK2 sK0]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 X0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 sK0 X0 sK0]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [l12 X0 sK0 sK2]
  have l16 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54245 X0 X1 sK0]
    conv => enter [1, 2]; rw [l12 X0 sK0 sK2]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 sK0]
    conv => enter [1]; rw [← l16 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation4280_implies_Equation54262 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54262 G := by
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
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4280 sK0 sK1 sK0]
    conv => enter [1]; rw [h4280 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]
  conv => enter [1]; rw [l2 y z z]

theorem Equation4512_54262_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54262 : Equation54262 G) : Equation4280 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54262 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54262 X0 sK0 sK0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54262 X0 sK2 sK2]
  have l4 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54262 X0 X1 sK2]
  have l5 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [← l4 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l6 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l5 X0 sK2]
    conv => enter [1]; rw [h54262 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l7 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l6 X0 sK2]
    conv => enter [1]; rw [h54262 sK2 (sK2 ◇ sK2) sK0]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l7 X0 sK2 sK0]
  have l9 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK2 sK1]
    conv => enter [1]; rw [l10 sK2 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l12 x x y z]

@[equational_result]
theorem Equation4280_implies_Equation54298 (G : Type*) [Magma G] (h4280 : Equation4280 G) : Equation54298 G := by
  have l0 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK3 sK3 sK0]
    conv => enter [1]; rw [h4280 sK3 X0 sK0]
  have l1 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h4280 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK3]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4280 sK3 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 X0 sK3 sK0]
  have l3 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4280 sK1 sK2 sK1]
    conv => enter [1]; rw [h4280 sK1 sK3 sK0]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 X0]
    conv => enter [1, 2]; rw [l3 sK2 sK2 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y w z]
  conv => enter [1]; rw [l4 w z z]

theorem Equation4512_54298_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54298 : Equation54298 G) : Equation4280 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54298 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X1)) := by
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
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation4360_implies_Equation4287 (G : Type*) [Magma G] (h4360 : Equation4360 G) : Equation4287 G := by
  intro x y z
  conv => enter [1]; rw [h4360 x x y z]

@[equational_result]
theorem Equation4287_implies_Equation4360 (G : Type*) [Magma G] (h4287 : Equation4287 G) : Equation4360 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4287 X0 sK3 sK2]
    conv => enter [1]; rw [h4287 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4360_implies_Equation4340 (G : Type*) [Magma G] (h4360 : Equation4360 G) : Equation4340 G := by
  intro x y z
  conv => enter [1]; rw [h4360 x y y z]

@[equational_result]
theorem Equation4340_implies_Equation4360 (G : Type*) [Magma G] (h4340 : Equation4340 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [← h4340 X0 sK3 sK0]
    conv => enter [1]; rw [h4340 X0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4360_4512_implies_Equation54360 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54360 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [h4360 X0 sK0 sK3 X0]
    conv => enter [1]; rw [h4360 X0 X0 sK3 sK2]
  have l1 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 X1 (sK2 ◇ sK3) sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK3 sK0]
  have l2 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l1 X0 X0 sK2 sK3 sK0]
  have l3 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ sK3) ◇ sK3) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h4360 sK0 sK2 sK3 sK3]
    conv => enter [1]; rw [h4512 sK0 sK3 sK3]
  have l4 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK0 ◇ sK3) ◇ sK3)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4360 X0 sK1 (sK2 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK2 sK3]
  have l5 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l4 X0 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h4360 X0 (X0 ◇ sK3) sK3 sK2]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l5 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

@[equational_result]
theorem Equation54360_implies_Equation4360 (G : Type*) [Magma G] (h54360 : Equation54360 G) : Equation4360 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h54360 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← h54360 X0 sK0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4360_4512_implies_Equation54375 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54375 G := by
  have l0 : ∀ X1 X0 sK2 sK3 X3 X2 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X3 ◇ (X2 ◇ sK3))) := by
    intro X1 X0 sK2 sK3 X3 X2
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK3 X2]
    conv => enter [1]; rw [h4360 X1 X0 (X2 ◇ sK3) X3]
  have l1 : ∀ X1 X0 sK2 sK3 X3 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X3 ◇ (sK3 ◇ sK3))) := by
    intro X1 X0 sK2 sK3 X3
    conv => enter [1]; rw [l0 X1 X0 sK2 sK3 X3 X1]
    conv => enter [1, 2]; rw [h4360 X3 X1 sK3 sK3]
  have l2 : ∀ X1 sK0 sK3 X0 sK2 : G, (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [h4360 X1 sK0 (sK3 ◇ sK3) X1]
    conv => enter [1]; rw [← l1 X1 X0 sK2 sK3 X1]
  have l3 : ∀ X1 sK0 sK3 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l2 X1 sK0 sK3 X1 sK2]
    conv => enter [1]; rw [h4360 X1 X1 (sK2 ◇ sK3) sK1]
  have l4 : ∀ X2 sK3 X0 X1 : G, (X2 ◇ (sK3 ◇ sK3)) = (X2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro X2 sK3 X0 X1
    conv => enter [1]; rw [h4360 X2 sK3 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ X2 sK3 X0 : G, (X2 ◇ (sK3 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X2 sK3 X0
    conv => enter [1]; rw [l4 X2 sK3 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK3 sK3]
  have l6 : ∀ X2 sK3 X0 sK2 : G, (X2 ◇ (sK3 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK3 X0 sK2
    conv => enter [1]; rw [l5 X2 sK3 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK3 sK3 sK2]
  have l7 : ∀ X2 sK3 sK1 sK2 : G, (X2 ◇ (sK3 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK3 sK1 sK2
    conv => enter [1]; rw [l6 X2 sK3 X2 sK2]
    conv => enter [1]; rw [h4360 X2 X2 (sK2 ◇ sK3) sK1]
  have l8 : ∀ X2 sK2 sK3 sK1 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK2 sK3 sK1
    conv => enter [1]; rw [h4360 X2 sK2 sK3 sK3]
    conv => enter [1]; rw [l7 X2 sK3 sK1 sK2]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation54375_implies_Equation4360 (G : Type*) [Magma G] (h54375 : Equation54375 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54375 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54375 X0 X3 X2 X0]
  have l1 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK3 X0]
    conv => enter [1]; rw [l0 X0 X0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4360_4512_implies_Equation54385 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54385 G := by
  have l0 : ∀ X0 sK0 sK4 sK3 : G, (X0 ◇ (sK0 ◇ sK4)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK0 sK4 sK3
    conv => enter [1]; rw [h4360 X0 sK0 sK4 X0]
    conv => enter [1]; rw [h4360 X0 X0 sK4 sK3]
  have l1 : ∀ X0 sK1 sK0 sK4 X1 sK3 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 X1 sK3
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 sK3]
    conv => enter [1]; rw [h4360 X0 sK1 (sK3 ◇ sK4) X1]
  have l2 : ∀ X0 sK1 sK0 sK4 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 sK2 sK3
    conv => enter [1]; rw [l1 X0 sK1 sK0 sK4 X0 sK3]
    conv => enter [1]; rw [h4360 X0 X0 (sK3 ◇ sK4) sK2]
  have l3 : ∀ sK0 sK3 sK4 : G, (sK0 ◇ (sK3 ◇ sK4)) = ((sK0 ◇ sK4) ◇ sK4) := by
    intro sK0 sK3 sK4
    conv => enter [1]; rw [h4360 sK0 sK3 sK4 sK4]
    conv => enter [1]; rw [h4512 sK0 sK4 sK4]
  have l4 : ∀ X0 sK2 sK3 sK4 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ ((sK0 ◇ sK4) ◇ sK4)) := by
    intro X0 sK2 sK3 sK4 sK0
    conv => enter [1]; rw [h4360 X0 sK2 (sK3 ◇ sK4) sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK3 sK4]
  have l5 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l4 X0 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [h4360 X0 (X0 ◇ sK4) sK4 sK3]
  have l6 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l5 sK2 sK2 sK3 sK4]
    conv => enter [1]; rw [l2 sK2 sK2 sK3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]

@[equational_result]
theorem Equation54385_implies_Equation4360 (G : Type*) [Magma G] (h54385 : Equation54385 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [h54385 X0 sK0 sK3 X0 sK0]
    conv => enter [1]; rw [← h54385 X0 sK2 sK3 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4360_4512_implies_Equation54314 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54314 G := by
  have l0 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l0 X2 sK2 sK1 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK1 sK2]
  have l2 : ∀ X2 sK2 sK1 X0 sK0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 sK0
    conv => enter [1]; rw [l1 X2 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK1 sK0]
  have l3 : ∀ X2 sK2 sK1 sK0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK1 sK0
    conv => enter [1]; rw [l2 X2 sK2 sK1 X2 sK0]
    conv => enter [1]; rw [h4360 X2 X2 (sK0 ◇ sK1) sK0]
  have l4 : ∀ X2 sK0 sK1 : G, (X2 ◇ (sK0 ◇ sK1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1
    conv => enter [1]; rw [h4360 X2 sK0 sK1 X2]
    conv => enter [1]; rw [l3 X2 X2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [h4360 x y z x]
  conv => enter [1]; rw [l4 x x z]

theorem Equation4512_54314_implies_Equation4360 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54314 : Equation54314 G) : Equation4360 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h54314 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54314 X0 X1 X2]
    conv => enter [1, 2]; rw [h54314 X0 X0 X2]
    conv => enter [1, 2]; rw [← h54314 X0 X1 X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X2)) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
    conv => enter [1]; rw [← l1 X3 X3 X2]
  have l3 : ∀ sK0 X0 sK3 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK3))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 X0 sK3 X1
    conv => enter [1, 2]; rw [h54314 sK0 X0 sK3]
    conv => enter [1]; rw [← h54314 sK0 X1 (sK0 ◇ sK3)]
  have l4 : ∀ sK0 sK3 X1 : G, (sK0 ◇ (sK0 ◇ sK3)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 X1
    conv => enter [1]; rw [← l2 sK0 sK0 sK0 sK3]
    conv => enter [1]; rw [l3 sK0 sK0 sK3 X1]
  have l5 : ∀ sK0 X0 sK3 sK2 : G, (sK0 ◇ (X0 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK0 X0 sK3 sK2
    conv => enter [1]; rw [h54314 sK0 X0 sK3]
    conv => enter [1]; rw [← h54314 sK0 sK2 sK3]
  have l6 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h54314 sK0 sK2 sK3]
    conv => enter [1, 2]; rw [h54314 sK0 sK0 sK3]
    conv => enter [1, 2]; rw [← h54314 sK0 sK2 sK3]
  have l7 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l4 sK0 sK3 sK3]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK0 ◇ sK3)]
  have l8 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK0 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l4 sK0 sK3 sK0]
    conv => enter [1]; rw [← h54314 sK0 sK2 sK3]
  have l9 : ∀ sK0 sK2 sK3 sK1 : G, (sK0 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [← l8 sK0 sK3 sK2]
    conv => enter [1]; rw [l4 sK0 sK3 sK1]
  have l10 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l8 sK0 sK3 sK2]
    conv => enter [1]; rw [l7 sK0 sK3]
  have l11 : ∀ sK0 sK2 sK3 X0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1, 2, 2]; rw [l9 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← h54314 sK0 X0 (sK1 ◇ (sK0 ◇ sK3))]
  have l12 : ∀ sK0 sK2 sK3 X0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1]; rw [← l2 sK0 sK0 sK0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l11 sK0 sK2 sK3 X0 sK1]
  have l13 : ∀ sK0 sK2 sK3 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK3]
    conv => enter [1]; rw [l12 sK0 sK2 sK3 X0 sK1]
  have l14 : ∀ sK0 sK3 X0 sK1 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK3 X0 sK1
    conv => enter [1]; rw [← l10 sK0 sK0 sK3]
    conv => enter [1]; rw [l13 sK0 sK0 sK3 X0 sK1]
  have l15 : ∀ sK0 sK3 X0 sK2 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)))) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK2 sK3]
    conv => enter [1]; rw [← h54314 sK0 X0 (sK2 ◇ sK3)]
  have l16 : ∀ sK0 sK3 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1, 2]; rw [← l2 sK0 (sK0 ◇ sK3) sK0 sK3]
    conv => enter [1]; rw [l15 sK0 sK3 X0 sK2]
  have l17 : ∀ sK0 sK3 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK3)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK3 sK0]
    conv => enter [1]; rw [l16 sK0 sK3 X0 sK2]
  have l18 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [← l8 sK0 sK3 sK2]
    conv => enter [1]; rw [l17 sK0 sK3 X0 sK2]
  have l19 : ∀ sK0 sK3 X0 sK2 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1]; rw [← l10 sK0 sK2 sK3]
    conv => enter [1]; rw [l18 sK0 sK2 sK3 X0]
  have l20 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ sK3) ◇ sK3) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l5 sK0 sK2 sK3 sK3]
    conv => enter [1]; rw [h4512 sK0 sK3 sK3]
  have l21 : ∀ sK0 sK3 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l20 sK0 sK0 sK3]
    conv => enter [1]; rw [l10 sK0 sK0 sK3]
  have l22 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (sK1 ◇ ((sK0 ◇ sK3) ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [← l21 sK0 sK3]
  have l23 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l22 sK1 sK0 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK3) sK3]
  have l24 : ∀ sK0 sK3 sK1 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l14 sK0 sK3 sK3 sK1]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK1 ◇ (sK0 ◇ sK3))]
  have l25 : ∀ sK0 sK3 sK1 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l21 sK0 sK3]
    conv => enter [1]; rw [l24 sK0 sK3 sK1]
  have l26 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ ((sK0 ◇ sK3) ◇ sK3)) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1, 2]; rw [l25 sK0 sK3 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK3) (sK1 ◇ (sK0 ◇ sK3))]
  have l27 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) sK3]
    conv => enter [1]; rw [l26 sK1 sK0 sK3]
  have l28 : ∀ sK0 sK3 sK2 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l19 sK0 sK3 sK3 sK2]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK2 ◇ sK3)]
  have l29 : ∀ sK0 sK3 sK2 : G, ((sK0 ◇ sK3) ◇ sK3) = ((sK0 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l21 sK0 sK3]
    conv => enter [1]; rw [l28 sK0 sK3 sK2]
  have l30 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ ((sK0 ◇ sK3) ◇ sK3)) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1, 2]; rw [l29 sK0 sK3 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK3) (sK2 ◇ sK3)]
  have l31 : ∀ sK1 sK0 sK3 sK2 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) sK3]
    conv => enter [1]; rw [l30 sK1 sK0 sK3 sK2]
  have l32 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h54314 sK1 (sK2 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h54314 sK1 (sK0 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK3) (sK2 ◇ sK3)]
  have l34 : ∀ sK1 X0 sK2 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 X0 sK2 sK3 X1
    conv => enter [1, 2]; rw [h54314 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← h54314 sK1 X1 (sK1 ◇ (sK2 ◇ sK3))]
  have l35 : ∀ sK1 sK2 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [← l2 sK1 sK1 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l34 sK1 sK1 sK2 sK3 X1]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 sK3 sK2]
  have l37 : ∀ sK1 sK0 sK3 sK2 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← l36 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l32 sK1 sK2 sK3]
  have l38 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l2 sK1 sK1 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l32 sK1 sK2 sK3]
  have l39 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l35 sK1 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK1 ◇ (sK2 ◇ sK3))]
  have l40 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l39 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l41 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l40 sK1 sK2 sK3 X0]
  have l42 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← h54314 sK1 (sK0 ◇ sK3) (sK0 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK3) (sK0 ◇ sK3)]
  have l43 : ∀ sK1 X0 sK0 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK3)))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 X0 sK0 sK3 X1
    conv => enter [1, 2]; rw [h54314 sK1 X0 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← h54314 sK1 X1 (sK1 ◇ (sK0 ◇ sK3))]
  have l44 : ∀ sK1 sK0 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X1
    conv => enter [1]; rw [← l2 sK1 sK1 sK1 (sK0 ◇ sK3)]
    conv => enter [1]; rw [l43 sK1 sK1 sK0 sK3 X1]
  have l45 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l42 sK1 sK0 sK3]
    conv => enter [1]; rw [l23 sK1 sK0 sK3]
  have l46 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l45 sK1 sK0 sK3]
    conv => enter [1]; rw [l37 sK1 sK0 sK3 sK2]
  have l47 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK3]
    conv => enter [1]; rw [← l46 sK1 sK0 sK3 sK2]
  have l48 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l44 sK1 sK0 sK3 sK1]
  have l49 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l44 sK1 sK0 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK1 ◇ (sK0 ◇ sK3))]
  have l50 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l49 sK1 sK0 sK3 sK2]
  have l51 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1, 2, 2]; rw [l50 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h54314 (sK1 ◇ (sK2 ◇ sK3)) X0 (sK1 ◇ (sK0 ◇ sK3))]
  have l52 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1, 1]; rw [l50 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) (sK1 ◇ (sK0 ◇ sK3)) X0]
  have l53 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l52 sK1 sK2 sK3 X0 sK0]
  have l54 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l41 sK1 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [l51 sK1 sK2 sK3 X0 sK0]
  have l55 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l54 sK1 sK2 sK3 X0 sK0]
  have l56 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l55 sK1 sK2 sK3 X0 sK0]
  have l57 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK1 ◇ (sK0 ◇ sK3)) ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK3 (sK1 ◇ (sK0 ◇ sK3)) sK0]
    conv => enter [1, 2]; rw [← l27 sK1 sK0 sK3]
  have l58 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l57 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l53 sK1 sK2 sK3 sK3 sK1]
  have l59 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2, 2]; rw [l58 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54314 sK1 X0 ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3)]
  have l60 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l59 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK3]
  have l61 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1, 2]; rw [← l2 sK1 sK1 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l60 sK1 sK2 sK3]
  have l62 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l61 sK1 sK2 sK3]
  have l63 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ (X0 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [l62 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54314 sK1 X0 sK3]
  have l64 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (X0 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l63 sK1 sK2 sK3 X0]
  have l65 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l64 sK1 sK2 sK3 sK2]
    conv => enter [1]; rw [l64 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l65 x y z w]

theorem Equation4360_4512_implies_Equation54322 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54322 G := by
  have l0 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l0 X2 sK2 sK1 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK1 sK2]
  have l2 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l1 X2 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK1 sK1]
  have l3 : ∀ X2 sK0 sK1 sK2 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X2 ◇ (sK2 ◇ sK1)) := by
    intro X2 sK0 sK1 sK2
    conv => enter [1]; rw [h4360 X2 sK0 (sK1 ◇ sK1) X2]
    conv => enter [1]; rw [← l2 X2 sK2 sK1 X2]
  have l4 : ∀ X2 sK1 sK0 : G, (X2 ◇ (sK1 ◇ sK1)) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X2 sK1 sK0
    conv => enter [1]; rw [h4360 X2 sK1 sK1 X2]
    conv => enter [1]; rw [← l3 X2 sK0 sK1 X2]
  intro x y z
  conv => enter [1]; rw [h4360 x y z z]
  conv => enter [1]; rw [l4 x z x]

@[equational_result]
theorem Equation54322_implies_Equation4360 (G : Type*) [Magma G] (h54322 : Equation54322 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54322 X0 X1 X2]
    conv => enter [1]; rw [← h54322 X0 X3 X2]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 sK2 sK3 X0]
    conv => enter [1]; rw [l0 X0 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4360_4512_implies_Equation54326 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54326 G := by
  have l0 : ∀ X2 sK2 sK3 X0 X1 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro X2 sK2 sK3 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l1 : ∀ X2 sK2 sK3 X0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK2 sK3 X0
    conv => enter [1]; rw [l0 X2 sK2 sK3 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK3 sK2]
  have l2 : ∀ X2 sK2 sK3 X0 sK0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l1 X2 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK3 sK0]
  have l3 : ∀ X2 sK2 sK3 sK1 sK0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l2 X2 sK2 sK3 X2 sK0]
    conv => enter [1]; rw [h4360 X2 X2 (sK0 ◇ sK3) sK1]
  have l4 : ∀ X2 sK0 sK3 sK1 : G, (X2 ◇ (sK0 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK0 sK3 sK1
    conv => enter [1]; rw [h4360 X2 sK0 sK3 X2]
    conv => enter [1]; rw [l3 X2 X2 sK3 sK1 sK0]
  have l5 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK3 sK1]
    conv => enter [1, 2]; rw [h4360 sK1 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation54326_implies_Equation4360 (G : Type*) [Magma G] (h54326 : Equation54326 G) : Equation4360 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [h54326 X0 sK0 sK3 sK0]
    conv => enter [1]; rw [← h54326 X0 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4360_4512_implies_Equation54348 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54348 G := by
  have l0 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l0 X2 sK2 sK1 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK1 sK2]
  have l2 : ∀ X2 sK2 sK1 X0 sK0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 sK0
    conv => enter [1]; rw [l1 X2 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK1 sK0]
  have l3 : ∀ X2 sK2 sK1 sK0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK1 sK0
    conv => enter [1]; rw [l2 X2 sK2 sK1 X2 sK0]
    conv => enter [1]; rw [h4360 X2 X2 (sK0 ◇ sK1) sK1]
  have l4 : ∀ X2 sK0 sK1 : G, (X2 ◇ (sK0 ◇ sK1)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1
    conv => enter [1]; rw [h4360 X2 sK0 sK1 X2]
    conv => enter [1]; rw [l3 X2 X2 sK1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK0 sK1]
    conv => enter [1]; rw [h4360 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l5 x z y]

@[equational_result]
theorem Equation54348_implies_Equation4360 (G : Type*) [Magma G] (h54348 : Equation54348 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54348 X0 X1 X2]
    conv => enter [1]; rw [← h54348 X0 X3 X2]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 sK2 sK3 X0]
    conv => enter [1]; rw [l0 X0 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4360_4512_implies_Equation54365 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54365 G := by
  have l0 : ∀ X1 X0 sK0 sK3 X3 X2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X3 ◇ (X2 ◇ sK3))) := by
    intro X1 X0 sK0 sK3 X3 X2
    conv => enter [1, 2]; rw [h4360 X0 sK0 sK3 X2]
    conv => enter [1]; rw [h4360 X1 X0 (X2 ◇ sK3) X3]
  have l1 : ∀ X1 X0 sK0 sK3 X3 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X3 ◇ (sK1 ◇ sK3))) := by
    intro X1 X0 sK0 sK3 X3 sK1
    conv => enter [1]; rw [l0 X1 X0 sK0 sK3 X3 X1]
    conv => enter [1, 2]; rw [h4360 X3 X1 sK3 sK1]
  have l2 : ∀ X1 sK2 sK1 sK3 X0 sK0 : G, (X1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK2 sK1 sK3 X0 sK0
    conv => enter [1]; rw [h4360 X1 sK2 (sK1 ◇ sK3) X1]
    conv => enter [1]; rw [l1 X1 X1 sK1 sK3 X0 sK0]
  have l3 : ∀ X1 sK2 sK1 sK3 sK0 : G, (X1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l2 X1 sK2 sK1 sK3 X1 sK0]
    conv => enter [1]; rw [h4360 X1 X1 (sK0 ◇ sK3) sK1]
  have l4 : ∀ X2 sK1 sK3 X0 X1 : G, (X2 ◇ (sK1 ◇ sK3)) = (X2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro X2 sK1 sK3 X0 X1
    conv => enter [1]; rw [h4360 X2 sK1 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ X2 sK1 sK3 X0 : G, (X2 ◇ (sK1 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X2 sK1 sK3 X0
    conv => enter [1]; rw [l4 X2 sK1 sK3 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK3 sK1]
  have l6 : ∀ X2 sK1 sK3 X0 sK0 : G, (X2 ◇ (sK1 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK1 sK3 X0 sK0
    conv => enter [1]; rw [l5 X2 sK1 sK3 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK1 sK3 sK0]
  have l7 : ∀ X2 sK1 sK3 sK0 : G, (X2 ◇ (sK1 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK1 sK3 sK0
    conv => enter [1]; rw [l6 X2 sK1 sK3 X2 sK0]
    conv => enter [1]; rw [h4360 X2 X2 (sK0 ◇ sK3) sK1]
  have l8 : ∀ X2 sK0 sK3 sK1 : G, (X2 ◇ (sK0 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK0 sK3 sK1
    conv => enter [1]; rw [h4360 X2 sK0 sK3 sK1]
    conv => enter [1]; rw [l7 X2 sK1 sK3 sK0]
  have l9 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK3 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation54365_implies_Equation4360 (G : Type*) [Magma G] (h54365 : Equation54365 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X2)) := by
    intro X0 X1 X2 X4
    conv => enter [1]; rw [h54365 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54365 X0 X4 X2 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4360_4512_implies_Equation54356 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54356 G := by
  have l0 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l0 X2 sK2 sK1 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK1 sK2]
  have l2 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [l1 X2 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK1 sK1]
  have l3 : ∀ X2 sK1 sK2 : G, (X2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (sK2 ◇ sK1)) := by
    intro X2 sK1 sK2
    conv => enter [1]; rw [h4360 X2 sK1 (sK1 ◇ sK1) X2]
    conv => enter [1]; rw [← l2 X2 sK2 sK1 X2]
  have l4 : ∀ X2 sK1 : G, (X2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X2 sK1
    conv => enter [1]; rw [l3 X2 sK1 X2]
    conv => enter [1]; rw [h4360 X2 X2 sK1 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4360 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l5 x z y]

@[equational_result]
theorem Equation54356_implies_Equation4360 (G : Type*) [Magma G] (h54356 : Equation54356 G) : Equation4360 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54356 X0 X1 X2]
    conv => enter [1]; rw [← h54356 X0 X3 X2]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 sK2 sK3 X0]
    conv => enter [1]; rw [l0 X0 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4360_4512_implies_Equation54380 (G : Type*) [Magma G] (h4360 : Equation4360 G) (h4512 : Equation4512 G) : Equation54380 G := by
  have l0 : ∀ X1 X0 sK0 sK3 X3 X2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X3 ◇ (X2 ◇ sK3))) := by
    intro X1 X0 sK0 sK3 X3 X2
    conv => enter [1, 2]; rw [h4360 X0 sK0 sK3 X2]
    conv => enter [1]; rw [h4360 X1 X0 (X2 ◇ sK3) X3]
  have l1 : ∀ X1 X0 sK0 sK3 X3 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X3 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 sK0 sK3 X3 sK2
    conv => enter [1]; rw [l0 X1 X0 sK0 sK3 X3 X1]
    conv => enter [1, 2]; rw [h4360 X3 X1 sK3 sK2]
  have l2 : ∀ X1 sK2 sK3 X0 sK0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [h4360 X1 sK2 (sK2 ◇ sK3) X1]
    conv => enter [1]; rw [l1 X1 X1 sK2 sK3 X0 sK0]
  have l3 : ∀ X1 sK2 sK3 sK1 sK0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l2 X1 sK2 sK3 X1 sK0]
    conv => enter [1]; rw [h4360 X1 X1 (sK0 ◇ sK3) sK1]
  have l4 : ∀ X2 sK2 sK3 X0 X1 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro X2 sK2 sK3 X0 X1
    conv => enter [1]; rw [h4360 X2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ X2 sK2 sK3 X0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK2 sK3 X0
    conv => enter [1]; rw [l4 X2 sK2 sK3 X0 X2]
    conv => enter [1, 2]; rw [h4360 X0 X2 sK3 sK2]
  have l6 : ∀ X2 sK2 sK3 X0 sK0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l5 X2 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h4360 X0 sK2 sK3 sK0]
  have l7 : ∀ X2 sK2 sK3 sK1 sK0 : G, (X2 ◇ (sK2 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l6 X2 sK2 sK3 X2 sK0]
    conv => enter [1]; rw [h4360 X2 X2 (sK0 ◇ sK3) sK1]
  have l8 : ∀ X2 sK0 sK3 sK1 : G, (X2 ◇ (sK0 ◇ sK3)) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro X2 sK0 sK3 sK1
    conv => enter [1]; rw [h4360 X2 sK0 sK3 X2]
    conv => enter [1]; rw [l7 X2 X2 sK3 sK1 sK0]
  have l9 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK3 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_54380_implies_Equation4360 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54380 : Equation54380 G) : Equation4360 G := by
  have l0 : ∀ sK1 sK0 sK3 sK2 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [h54380 sK1 (sK0 ◇ sK3) (sK2 ◇ sK3) sK1]
  have l1 : ∀ sK1 sK0 sK3 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK3 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [← h54380 sK1 X0 (sK2 ◇ sK3) sK1]
  have l2 : ∀ sK1 sK0 sK3 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ sK3)) = (sK1 ◇ (X0 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK0 sK3 sK2 sK2]
    conv => enter [1]; rw [← h54380 sK1 X0 sK3 sK2]
  have l3 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (X0 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l1 sK1 sK1 sK3 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 sK2 X0]
  have l4 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← l3 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4299_4512_implies_Equation4312 (G : Type*) [Magma G] (h4299 : Equation4299 G) (h4512 : Equation4512 G) : Equation4312 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4299 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4299 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4299 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← h4299 sK1 sK2 (sK1 ◇ sK1)]
  have l2 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK1]
  have l4 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4299 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation4312_implies_Equation4299 (G : Type*) [Magma G] (h4312 : Equation4312 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [h4312 x y z x]

@[equational_result]
theorem Equation4300_implies_Equation4330 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4330 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4300 sK1 sK0 sK2]
    conv => enter [1]; rw [h4300 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4330_implies_Equation4300 (G : Type*) [Magma G] (h4330 : Equation4330 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4330 sK1 sK0 sK2]
    conv => enter [1]; rw [h4330 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4300_implies_Equation4374 (G : Type*) [Magma G] (h4300 : Equation4300 G) : Equation4374 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK2 sK3 X0]
    conv => enter [1]; rw [h4300 sK2 sK3 X1]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation4374_implies_Equation4300 (G : Type*) [Magma G] (h4374 : Equation4374 G) : Equation4300 G := by
  intro x y z
  conv => enter [1]; rw [h4374 x x y z]

theorem Equation4300_4512_implies_Equation54524 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54524 G := by
  have l0 : ∀ X0 sK0 sK2 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK0 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h4300 sK0 (sK2 ◇ sK3) X1]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK2 sK3 X0]
    conv => enter [1]; rw [h4300 sK2 sK3 X1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK3 sK0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK3 sK1]
  have l4 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK3)]
  have l5 : ∀ X0 sK2 sK3 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 sK1
    conv => enter [1]; rw [l4 X0 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK3 sK1]
  have l6 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK3 sK3]
    conv => enter [1]; rw [← l5 X0 sK2 sK3 sK3 sK3]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

@[equational_result]
theorem Equation54524_implies_Equation4300 (G : Type*) [Magma G] (h54524 : Equation54524 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54524 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54524 X0 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54602 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54602 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK2 sK3 X0]
    conv => enter [1]; rw [h4300 sK2 sK3 X1]
  have l1 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [← h4300 sK3 (sK2 ◇ sK3) sK0]
    conv => enter [1]; rw [h4300 sK3 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h4300 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK3)]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK3 sK3]
  have l4 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [← l3 sK2 sK3 sK0]
  have l5 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK3 sK2 sK3 sK2]
    conv => enter [1]; rw [← l4 sK0 sK3 sK2]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK3]
    conv => enter [1]; rw [l5 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

@[equational_result]
theorem Equation54602_implies_Equation4300 (G : Type*) [Magma G] (h54602 : Equation54602 G) : Equation4300 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h54602 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← h54602 X1 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54655 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54655 G := by
  have l0 : ∀ sK1 sK0 sK3 sK4 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK3 sK4 X0
    conv => enter [1]; rw [← h4300 sK0 (sK3 ◇ sK4) sK1]
    conv => enter [1]; rw [h4300 sK0 (sK3 ◇ sK4) X0]
  have l1 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4300 sK3 sK4 X0]
    conv => enter [1]; rw [h4300 sK3 sK4 X1]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK1 sK0 sK3 sK4 X0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK3 sK4 X0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK3 sK4 X0]
    conv => enter [1, 2]; rw [l2 sK0 sK3 sK4 sK2]
  have l4 : ∀ X0 sK3 sK4 X1 X2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (X2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK3 sK4 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK3 ◇ sK4)]
  have l5 : ∀ X0 sK3 sK4 X1 sK2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 X1 sK2
    conv => enter [1]; rw [l4 X0 sK3 sK4 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK3 sK4 sK2]
  have l6 : ∀ sK1 sK0 sK3 sK4 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 sK3 sK4 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK3 sK4 sK1 sK1]
    conv => enter [1]; rw [← l5 X0 sK3 sK4 sK1 sK1]
  have l7 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0 sK3 sK4 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u]

@[equational_result]
theorem Equation54655_implies_Equation4300 (G : Type*) [Magma G] (h54655 : Equation54655 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54655 sK0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h54655 sK2 sK0 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4300_4512_implies_Equation54412 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54412 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4300 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0 sK0]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4300 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4300 sK0 sK1 sK2]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4300 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation54412_implies_Equation4300 (G : Type*) [Magma G] (h54412 : Equation54412 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54412 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54412 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54506 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54506 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4300 sK1 sK0 sK2]
    conv => enter [1]; rw [h4300 sK1 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4300 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0 sK2]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← l2 sK1 sK0 X0 X0]
  have l4 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l3 X0 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK2 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l5 z y x]

@[equational_result]
theorem Equation54506_implies_Equation4300 (G : Type*) [Magma G] (h54506 : Equation54506 G) : Equation4300 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h54506 X0 sK0 sK1]
    conv => enter [1]; rw [← h54506 X1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54628 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54628 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4300 sK2 sK3 X0]
    conv => enter [1]; rw [h4300 sK2 sK3 X1]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0]
  have l2 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l0 X0 sK2 sK3 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK3)]
  have l3 : ∀ X0 sK2 sK3 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 sK1
    conv => enter [1]; rw [l2 X0 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK3 sK1]
  have l4 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l3 X0 sK2 sK3 sK1 sK1]
  have l5 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l4 sK1 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l5 w y z]

@[equational_result]
theorem Equation54628_implies_Equation4300 (G : Type*) [Magma G] (h54628 : Equation54628 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54628 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54628 X0 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54429 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54429 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4300 sK0 sK1 sK2]
    conv => enter [1]; rw [h4300 sK0 sK1 sK1]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4300 sK0 sK1 sK2]
    conv => enter [1]; rw [h4300 sK0 sK1 X0]
  have l2 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1, 2]; rw [← h4300 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4300 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4300 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [← l0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l2 X0 sK2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4300 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK0]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_54429_implies_Equation4300 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54429 : Equation54429 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54429 X0 sK0 sK1]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 z x y]

theorem Equation4300_4512_implies_Equation54447 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54447 G := by
  have l0 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4300 sK1 sK3 sK2]
    conv => enter [1]; rw [h4300 sK1 sK3 sK0]
  have l1 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK1 ◇ sK3)) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [← h4300 sK1 sK3 sK2]
    conv => enter [1]; rw [h4300 sK1 sK3 X0]
  have l2 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [← h4300 sK1 sK3 sK2]
    conv => enter [1]; rw [h4300 sK1 (sK1 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h4300 sK1 sK3 sK2]
  have l3 : ∀ sK1 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK3 X0 X1
    conv => enter [1]; rw [h4300 sK1 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l4 : ∀ sK1 sK3 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK3 X0 sK2
    conv => enter [1]; rw [l3 sK1 sK3 X0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK1 sK3 sK2]
  have l5 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l4 sK1 sK3 sK1 sK2]
  have l6 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [l1 sK2 sK1 sK3 sK1]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]
  conv => enter [1]; rw [l6 w y z]

@[equational_result]
theorem Equation54447_implies_Equation4300 (G : Type*) [Magma G] (h54447 : Equation54447 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54447 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54447 X0 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54489 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54489 G := by
  have l0 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4300 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← h4300 y z x]
  conv => enter [1]; rw [l1 y z z]

@[equational_result]
theorem Equation54489_implies_Equation4300 (G : Type*) [Magma G] (h54489 : Equation54489 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54489 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54489 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

theorem Equation4300_4512_implies_Equation54576 (G : Type*) [Magma G] (h4300 : Equation4300 G) (h4512 : Equation4512 G) : Equation54576 G := by
  have l0 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h4300 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK3)]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l0 sK2 sK3 X0 sK2]
  have l2 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l1 sK2 sK3 sK2]
    conv => enter [1]; rw [h4300 sK2 (sK2 ◇ sK3) sK1]
  intro x y z w
  conv => enter [1]; rw [← h4300 y z x]
  conv => enter [1]; rw [l2 y z w]

@[equational_result]
theorem Equation54576_implies_Equation4300 (G : Type*) [Magma G] (h54576 : Equation54576 G) : Equation4300 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54576 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54576 sK2 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4301_4512_implies_Equation4311 (G : Type*) [Magma G] (h4301 : Equation4301 G) (h4512 : Equation4512 G) : Equation4311 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4301 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4301 sK1 X0 sK1]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4301 X0 X1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← h4301 sK1 sK2 X0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l1 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4301 (sK1 ◇ sK2) X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4301 sK1 sK2 (sK1 ◇ sK2)]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) sK1 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4301 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4301 sK1 sK2 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4301 sK1 sK2 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK1 X0 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4301 sK1 sK2 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l5 sK1 sK2]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2]
  have l13 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4301 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 X0]
  have l14 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l15 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l14 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2]
  have l16 : ∀ X2 X0 sK1 sK2 : G, (X2 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X2 X0 sK1 sK2
    conv => enter [1]; rw [← h4301 X0 X2 X2]
    conv => enter [1]; rw [l15 X0 X2 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l16 z w x y]

@[equational_result]
theorem Equation4311_implies_Equation4301 (G : Type*) [Magma G] (h4311 : Equation4311 G) : Equation4301 G := by
  have l0 : ∀ sK2 sK0 X2 X3 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X2 ◇ (X3 ◇ X2)) := by
    intro sK2 sK0 X2 X3
    conv => enter [1]; rw [← h4311 sK2 sK2 sK2 sK0]
    conv => enter [1]; rw [h4311 sK2 sK2 X2 X3]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4311 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation4315 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4315 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4339 X0 sK1 sK2]
    conv => enter [1]; rw [h4339 X0 sK1 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4315_implies_Equation4339 (G : Type*) [Magma G] (h4315 : Equation4315 G) : Equation4339 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4315 X0 sK1 sK2]
    conv => enter [1]; rw [h4315 X0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation4339_implies_Equation4357 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation4357 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4357_implies_Equation4339 (G : Type*) [Magma G] (h4357 : Equation4357 G) : Equation4339 G := by
  intro x y z
  conv => enter [1]; rw [h4357 x y y z]

@[equational_result]
theorem Equation4339_implies_Equation54341 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54341 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w x]

@[equational_result]
theorem Equation54341_implies_Equation4339 (G : Type*) [Magma G] (h54341 : Equation54341 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54341 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54341 X0 X1 X3 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54342 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54342 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 (sK0 ◇ sK2)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation54342_implies_Equation4339 (G : Type*) [Magma G] (h54342 : Equation54342 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54342 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54342 X0 X1 X3 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54344 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54344 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 (sK0 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation54344_implies_Equation4339 (G : Type*) [Magma G] (h54344 : Equation54344 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54344 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54344 X0 X1 X3 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK1 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54345 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54345 G := by
  have l0 : ∀ X0 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4339 X0 sK3 sK4]
    conv => enter [1]; rw [h4339 X0 sK3 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation54345_implies_Equation4339 (G : Type*) [Magma G] (h54345 : Equation54345 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54345 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54345 X0 X1 X3 X0 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK1 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54329 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54329 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4339 X0 sK1 sK2]
    conv => enter [1]; rw [h4339 X0 sK1 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z x]

@[equational_result]
theorem Equation54329_implies_Equation4339 (G : Type*) [Magma G] (h54329 : Equation54329 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54329 X0 X1 X2]
    conv => enter [1]; rw [← h54329 X0 X1 X3]
  intro x y z
  conv => enter [1]; rw [l0 x y y z]

@[equational_result]
theorem Equation4339_implies_Equation54330 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54330 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4339 X0 sK1 sK2]
    conv => enter [1]; rw [h4339 X0 sK1 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z x]

theorem Equation4512_54330_implies_Equation4339 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54330 : Equation54330 G) : Equation4339 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK1 sK2 X0]
    conv => enter [1]; rw [h54330 sK1 (sK1 ◇ sK1) (sK2 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h54330 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X1]
  have l12 : ∀ sK1 X1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [← l11 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l13 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l9 sK1 sK1 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l12 sK1 X1 sK1 sK1]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54330 X0 X1 X2]
    conv => enter [1]; rw [← h54330 X0 X1 X3]
  have l17 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (X1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← h54330 X1 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (X0 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← h54330 X0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← l15 sK1 X0]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h54330 sK0 (sK1 ◇ sK2) X0]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h54330 sK0 (sK1 ◇ sK1) X0]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h54330 sK1 sK2 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h54330 (sK1 ◇ sK2) X0 X1]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h54330 sK0 (sK1 ◇ sK2) (X0 ◇ ((sK1 ◇ sK2) ◇ X0))]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l21 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l24 sK1 sK2 X0]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l33 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← l25 sK0 sK1 X1]
  have l34 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l33 sK0 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l34 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK1 ◇ sK1) X0]
  have l37 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l36 sK0 sK1 X0]
    conv => enter [1]; rw [l35 sK0 sK1 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [l37 sK0 sK1 sK0 sK2]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2 X0]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l42 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54332 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54332 G := by
  have l0 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h4339 X0 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 x y x w z]

@[equational_result]
theorem Equation54332_implies_Equation4339 (G : Type*) [Magma G] (h54332 : Equation54332 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X2 X4
    conv => enter [1]; rw [h54332 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54332 X0 X1 X4 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54333 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54333 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4339 X0 sK1 sK2]
    conv => enter [1]; rw [h4339 X0 sK1 (sK1 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z x]

theorem Equation4512_54333_implies_Equation4339 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54333 : Equation54333 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h54333 sK0 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54333 X0 X1 X2]
    conv => enter [1]; rw [← h54333 X0 X1 X3]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h54333 sK0 (sK1 ◇ sK1) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK0)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 (sK1 ◇ sK2) X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l18 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54334 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54334 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4339 sK0 sK1 sK2]
    conv => enter [1]; rw [h4339 sK0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_54334_implies_Equation4339 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54334 : Equation54334 G) : Equation4339 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54334 X0 X1 X2]
    conv => enter [1]; rw [← h54334 X0 X1 X3]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h54334 sK1 sK1 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [l0 sK1 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← h54334 sK1 sK1 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54334 sK0 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation4339_implies_Equation54336 (G : Type*) [Magma G] (h4339 : Equation4339 G) : Equation54336 G := by
  have l0 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4339 X0 sK2 sK3]
    conv => enter [1]; rw [h4339 X0 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK2 sK3]
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x y w z]

@[equational_result]
theorem Equation54336_implies_Equation4339 (G : Type*) [Magma G] (h54336 : Equation54336 G) : Equation4339 G := by
  have l0 : ∀ X0 X1 X2 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X2 X4
    conv => enter [1]; rw [h54336 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54336 X0 X1 X4 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK1 X0]
    conv => enter [1]; rw [l0 X0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4331_implies_Equation4337 (G : Type*) [Magma G] (h4331 : Equation4331 G) : Equation4337 G := by
  have l0 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [h4331 sK0 sK0 X0]
    conv => enter [1]; rw [h4331 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK0 sK3 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK3 X1 X0
    conv => enter [1, 2]; rw [← h4331 sK0 sK0 sK3]
    conv => enter [1]; rw [l0 sK0 X1 X0]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4331 sK0 sK0 sK3]
    conv => enter [1]; rw [h4331 sK0 sK0 X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4331 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4331 X0 sK2 sK1]
  have l4 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l3 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK3]
  have l5 : ∀ X0 sK0 sK3 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK3 sK1 sK2
    conv => enter [1]; rw [← h4331 (sK3 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0 sK3]
  have l6 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK0 sK3 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l6 sK0 sK3 sK1 sK2]
  have l8 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4331 (sK1 ◇ (sK2 ◇ sK1)) (sK3 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK3 sK0]
  have l9 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 sK3 sK0 sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK1 sK2]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← h4331 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l10 sK1 sK2]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l11 X0 sK1 sK2]
  have l13 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← h4331 (sK1 ◇ (sK2 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l13 X1 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

@[equational_result]
theorem Equation4337_implies_Equation4331 (G : Type*) [Magma G] (h4337 : Equation4337 G) : Equation4331 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4337 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4337 sK0 sK0 sK1 sK1]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← h4337 (sK1 ◇ sK1) sK1 X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4337 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l4 X0 X1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z y]

theorem Equation3309_4512_implies_Equation41736 (G : Type*) [Magma G] (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation41736 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3309 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3309 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3309 X0 sK1]
    conv => enter [1]; rw [← l1 X0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3309 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h3309 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_41736_implies_Equation3309 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation3309 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41736 sK1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l10 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h41736 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK1]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h41736 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X2]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41736 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l15 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1, 2]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X0)]
  have l20 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l21 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ X0))]
  have l24 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l25 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l27 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l23 sK1 X0]
  have l28 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l24 X0 X1 X2]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1, 2]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [← l27 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l26 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1, 2]; rw [← l32 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ sK1)]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← l32 sK1]
  have l39 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l41 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [← l39 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41736 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l52 sK0 sK1]
  have l54 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l28 X0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK0 sK1]
  have l55 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l54 X0 sK0 sK1]
  have l56 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l53 X0 sK0 sK1]
    conv => enter [1]; rw [l55 X0 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l56 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l48 x y]
  conv => enter [1]; rw [l57 x y]

theorem Equation3309_4512_implies_Equation41746 (G : Type*) [Magma G] (h3309 : Equation3309 G) (h4512 : Equation4512 G) : Equation41746 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3309 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3309 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2]; rw [← h3309 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3309 X0 X0]
    conv => enter [1]; rw [← l4 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3309 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l5 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_41746_implies_Equation3309 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41746 : Equation41746 G) : Equation3309 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41746 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41746 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41746 sK1 X0]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1, 2]; rw [l1 sK1 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h41746 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l11 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

end Semigroup5
