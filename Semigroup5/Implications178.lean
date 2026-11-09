import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation4269_implies_Equation4316 (G : Type*) [Magma G] (h4269 : Equation4269 G) : Equation4316 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4316_implies_Equation4269 (G : Type*) [Magma G] (h4316 : Equation4316 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [h4316 x x y]

theorem Equation4269_4512_implies_Equation54030 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54030 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation54030_implies_Equation4269 (G : Type*) [Magma G] (h54030 : Equation54030 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54030 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54030 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation4269_4512_implies_Equation54038 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54038 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z z]

theorem Equation4512_54038_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54038 : Equation54038 G) : Equation4269 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54038 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation4269_4512_implies_Equation54042 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54042 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4269 sK1 sK2]
    conv => enter [1]; rw [h4269 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54042_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54042 : Equation54042 G) : Equation4269 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54042 sK0 (sK0 ◇ sK0) X0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h54042 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l9 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h54042 sK0 X2 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54042 sK0 sK0 X0 sK0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h54042 sK0 (sK1 ◇ sK0) X0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54042 sK0 X0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54042 sK0 X0 (sK1 ◇ sK0) sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l16 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X0 X1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54042 sK0 sK1 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54042 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54042 sK0 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK1]
  have l29 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [l28 sK0 sK0 X1 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l4 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l38 x y]

theorem Equation4269_4512_implies_Equation54010 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54010 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4269 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4269 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [l3 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_54010_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54010 : Equation54010 G) : Equation4269 G := by
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
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54010 X0 X1]
    conv => enter [1]; rw [← h54010 X0 X2]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54010 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54010 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4269_4512_implies_Equation54016 (G : Type*) [Magma G] (h4269 : Equation4269 G) (h4512 : Equation4512 G) : Equation54016 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 sK2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4269 sK0 sK1]
    conv => enter [1]; rw [h4269 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l3 x z]

theorem Equation4512_54016_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54016 : Equation54016 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h54016 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4270_implies_Equation4341 (G : Type*) [Magma G] (h4270 : Equation4270 G) : Equation4341 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4270 X0 sK1]
    conv => enter [1]; rw [h4270 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4341_implies_Equation4270 (G : Type*) [Magma G] (h4341 : Equation4341 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [h4341 x x y]

@[equational_result]
theorem Equation4271_implies_Equation4285 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4285 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z x]

@[equational_result]
theorem Equation4285_implies_Equation4271 (G : Type*) [Magma G] (h4285 : Equation4285 G) : Equation4271 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4285 sK0 sK0 X0]
    conv => enter [1]; rw [h4285 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4289 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4289 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x x y z w]

@[equational_result]
theorem Equation4289_implies_Equation4271 (G : Type*) [Magma G] (h4289 : Equation4289 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [h4289 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4317 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4317 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation4317_implies_Equation4271 (G : Type*) [Magma G] (h4317 : Equation4317 G) : Equation4271 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4317 sK0 sK0 X0]
    conv => enter [1]; rw [h4317 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4271_implies_Equation4319 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4319 G := by
  have l0 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK1]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y x z w]

@[equational_result]
theorem Equation4319_implies_Equation4271 (G : Type*) [Magma G] (h4319 : Equation4319 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [h4319 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4342 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4342 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4342_implies_Equation4271 (G : Type*) [Magma G] (h4342 : Equation4342 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [h4342 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4359 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4359 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4359_implies_Equation4271 (G : Type*) [Magma G] (h4359 : Equation4359 G) : Equation4271 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h4359 X0 sK0 sK0 sK1]
    conv => enter [1]; rw [h4359 X0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation4361 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation4361 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation4361_implies_Equation4271 (G : Type*) [Magma G] (h4361 : Equation4361 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [h4361 x x x y z]

@[equational_result]
theorem Equation4271_implies_Equation54353 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54353 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 (sK2 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_54353_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54353 : Equation54353 G) : Equation4271 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h54353 (sK0 ◇ sK0) X0 sK0 X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X0)]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l4 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54353 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54353 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h54353 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)]
    conv => enter [1, 2]; rw [l17 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l22 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54353 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 X0]
  have l27 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l29 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l30 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h54353 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l32 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l31 sK0 X0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l27 sK0 sK1 sK2 X0]
  have l34 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l33 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l35 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2 X0 X1]
  have l36 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h54353 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l38 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l40 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54353 (sK0 ◇ (sK1 ◇ sK2)) X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1, 2, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h54353 X1 (sK0 ◇ sK0) X2 (sK0 ◇ X0)]
  have l43 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54353 X1 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l44 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54353 X1 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l45 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54353 sK0 X0 (sK1 ◇ sK2) X1]
  have l46 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l41 sK0 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0 sK0]
  have l47 : ∀ X1 sK0 X2 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [← l42 X1 X2 sK0 X1]
    conv => enter [1]; rw [← h54353 X1 (sK0 ◇ (sK0 ◇ sK0)) X2 X1]
  have l48 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [l44 X1 sK0 X2]
    conv => enter [1]; rw [← l47 X1 sK0 X2]
  have l49 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l48 X1 sK0 X1]
    conv => enter [1]; rw [← l43 X1 sK0 X1]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [l49 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 sK0 sK0]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l46 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l55 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l54 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54353 sK0 X1 X0 (sK1 ◇ sK2)]
  have l56 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l49 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [l55 sK0 sK1 sK2 X1 X0]
  have l57 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l53 sK0 sK0 sK0]
    conv => enter [1]; rw [l56 sK0 sK0 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l57 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54358 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54358 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w x]

theorem Equation4512_54358_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54358 : Equation54358 G) : Equation4271 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54358 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h54358 sK0 X1 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [l2 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54358 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54358 sK0 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0]
  intro x y z
  conv => enter [1]; rw [← l11 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54359 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54359 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 (sK0 ◇ sK2)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_54359_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54359 : Equation54359 G) : Equation4271 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [← h54359 (sK0 ◇ sK0) X1 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54359 sK0 X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ X0)]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l7 sK0 sK1 (sK2 ◇ X0)]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 X0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l16 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l7 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l16 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X2]
  have l18 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54359 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK2 ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l10 sK0 (sK2 ◇ X0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ X0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ X0)]
  have l22 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 X0]
  have l23 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X2))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l17 sK0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X2]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK0 X0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 X0]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK2 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 sK0]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 ((sK1 ◇ sK2) ◇ X0)]
  have l29 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l23 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h54359 (sK0 ◇ sK0) X2 X0 sK0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l10 sK0 ((sK1 ◇ sK2) ◇ X0)]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54359 sK0 sK0 sK2 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54359 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l33 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 sK0]
  have l34 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ X0) X2]
    conv => enter [1]; rw [l29 sK0 sK0 X0 X2]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 sK0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) X0]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54359 sK0 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l33 sK0 X0 sK1 sK2]
  have l39 : ∀ sK0 X2 X0 : G, (sK0 ◇ (X2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l10 sK0 X2]
    conv => enter [1]; rw [l34 sK0 X2 X0]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54359 sK0 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2 sK0]
  have l41 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l36 sK0 sK0 sK2 X0]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0 X0]
  have l43 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l45 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l39 sK0 X0 sK0]
    conv => enter [1]; rw [l41 sK0 X0 sK2]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← l39 sK0 X0 sK0]
  have l47 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l43 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l39 sK0 X0 sK0]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l50 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l47 sK0 sK1 sK2 X0]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l50 sK0 sK1 sK2 sK0]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l54 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l52 sK0 sK0 sK0]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l56 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l57 sK0 sK0 sK2]
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK0 ◇ sK2)) sK2]
  have l60 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l59 sK0 sK2]
  have l61 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [l60 sK0 sK2]
  have l62 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l63 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l64 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l63 sK0 X0 sK0 sK2]
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK0 ◇ sK2)) sK2]
  have l65 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l61 sK0 sK0]
    conv => enter [1]; rw [← l64 sK0 X0 sK0]
  have l66 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ sK0) X1]
  have l67 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l66 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l68 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l67 sK0 X1 X0]
    conv => enter [1]; rw [← h54359 sK0 X1 X0 sK0]
  have l69 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l65 sK0 X1]
    conv => enter [1]; rw [l68 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l69 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54361 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54361 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 (sK0 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_54361_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54361 : Equation54361 G) : Equation4271 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54361 X0 X1 X2 X3]
    conv => enter [1]; rw [h54361 X0 X2 (X3 ◇ X3) X4]
  have l7 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54361 X0 X1 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← h54361 X0 X1 (sK0 ◇ sK0) sK0]
  have l9 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54361 X0 X1 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54361 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54361 X0 X3 X2 X0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l8 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l12 : ∀ X0 X1 X2 X4 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X4 ◇ X4) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 X4 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 X0 X4]
    conv => enter [1]; rw [h54361 X0 (X0 ◇ X0) (X4 ◇ X4) sK0]
  have l13 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 X2 X0 sK0]
    conv => enter [1]; rw [l9 X0 (X0 ◇ X0) sK0 sK1 sK2]
  have l14 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h54361 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
  have l15 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l14 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 X1 X2 sK0 X0 X0]
    conv => enter [1]; rw [l11 X0 (sK0 ◇ (X0 ◇ X0)) sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [h54361 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h54361 (sK0 ◇ sK0) sK0 X0 sK0]
  have l19 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54361 sK0 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l22 sK0 sK0]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h54361 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h54361 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54361 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l30 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) X0]
  have l31 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l16 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) X0 sK0]
  have l32 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l24 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l33 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h54361 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 sK0 sK0]
    conv => enter [1]; rw [← l33 sK0 X0 sK0 sK0]
  have l35 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0) X0 X1]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l36 sK0 sK0 X0]
    conv => enter [1]; rw [← l35 sK0 X0 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l37 sK0 X0]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [← l38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l40 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54362 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54362 G := by
  have l0 : ∀ X0 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK3 sK4]
    conv => enter [1]; rw [h4271 X0 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

theorem Equation4512_54362_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54362 : Equation54362 G) : Equation4271 G := by
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
  have l9 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    conv => enter [1]; rw [h54362 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [h54362 X0 X2 (X3 ◇ X4) X5 X6]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54362 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ X0 X1 X2 X5 X6 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X5 ◇ X6) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X5 X6 sK0
    conv => enter [1]; rw [l9 X0 X1 X2 X0 X0 X5 X6]
    conv => enter [1]; rw [l10 X0 (X0 ◇ X0) (X5 ◇ X6) sK0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 X0 X0 sK0]
    conv => enter [1]; rw [l10 X0 (X0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [h54362 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l14 : ∀ X0 X1 X2 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK2) sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h54362 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54362 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0) sK0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h54362 (sK0 ◇ sK0) sK0 X0 sK0 sK0]
  have l18 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54362 sK0 X0 (sK1 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK1 sK2 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l22 sK0 sK0]
  have l25 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54362 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
    conv => enter [1]; rw [← l24 sK0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
  have l31 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54362 sK0 (sK0 ◇ sK0) X0 sK0 (sK1 ◇ sK2)]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l25 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l31 sK0 X0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54362 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 sK2 X0]
  have l34 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 sK0 sK1 sK2 X0]
  have l35 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54362 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0 X0 sK1 sK2]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l35 sK0 X1 sK0 sK0]
    conv => enter [1]; rw [← h54362 sK0 X0 X1 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54368 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54368 G := by
  have l0 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  have l1 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54368_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54368 : Equation54368 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [← h54368 sK0 (sK1 ◇ sK2) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54368 sK0 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h54368 sK0 (sK0 ◇ sK0) X1 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54368 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1]; rw [l4 sK0 X0 ((sK0 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [← l4 sK0 X0 ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0 sK1 sK2 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54368 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54368 sK0 sK0 (sK1 ◇ sK2) sK0]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 X0]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54368 X0 X1 X2 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← l16 sK0 X0 X0 (X1 ◇ X0)]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0]
  intro x y z
  conv => enter [1]; rw [← l18 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54369 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54369 G := by
  have l0 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  have l1 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54369_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54369 : Equation54369 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54369 X0 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54369 sK0 (sK0 ◇ sK0) X0 X1]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54369 X0 sK0 X1 sK0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54369 sK0 sK0 X1 X0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h54369 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 X1 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54369 X0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l9 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 (sK1 ◇ sK2)]
  have l13 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h54369 X0 X1 X2 sK0]
    conv => enter [1]; rw [h54369 X0 sK0 (X1 ◇ X1) X3]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 X0 sK0]
    conv => enter [1]; rw [← h54369 X0 sK0 sK0 X0]
  have l15 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l14 X0 X1 X2 sK0]
    conv => enter [1]; rw [l12 X0 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l16 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54371 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54371 G := by
  have l0 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK2 sK0]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54371_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54371 : Equation54371 G) : Equation4271 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54371 X0 (sK0 ◇ sK0) X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54371 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54371 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 sK0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54371 X0 sK0 X1 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h54371 sK0 (sK0 ◇ sK0) X1 X0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54371 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X1 X0]
    conv => enter [1]; rw [l12 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l10 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l9 X0 sK0 X1]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 X0 sK0 X1]
  have l17 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h54371 X0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l15 X0 sK0 X1]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l7 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 X0 sK0 X1]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l18 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l14 sK0 sK0 sK0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 X1 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l24 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54371 X1 X2 X3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l20 sK0 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l25 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l24 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l19 X1 sK0 X1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l23 sK0 sK0 sK1 sK2]
  have l27 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54371 sK0 sK0 X0 (sK1 ◇ sK2)]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK0 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0]
  intro x y z
  conv => enter [1]; rw [← l31 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54372 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54372 G := by
  have l0 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l1 : ∀ X0 sK3 sK4 sK0 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK3 sK4 sK0
    conv => enter [1]; rw [← h4271 X0 sK3 sK4]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [← l0 sK2 sK1 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_54372_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54372 : Equation54372 G) : Equation4271 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54372 X0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← h54372 X0 sK0 (sK1 ◇ sK2) X0 sK0]
  have l1 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l0 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54372 X1 sK0 (sK1 ◇ sK2) X0 sK0]
  have l2 : ∀ sK0 X1 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54372 sK0 sK0 X1 X0 (sK1 ◇ sK2)]
  have l3 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 X1 sK0 sK1 sK2]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 X1]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54372 X0 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l4 sK0 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h54372 X0 sK0 (sK1 ◇ sK2) sK0 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54373 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54373 G := by
  have l0 : ∀ X0 sK0 sK3 sK1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X0 ◇ (sK3 ◇ sK1)) := by
    intro X0 sK0 sK3 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4271 X0 sK3 sK1]
  have l1 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK1)) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54373_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54373 : Equation54373 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54373 sK0 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54373 sK0 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54373 sK0 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54373 sK0 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54373 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 X1]
  have l13 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 X1 sK0 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54373 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l17 sK0 (X2 ◇ X0)]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l19 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54374 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54374 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro X0 sK0 sK3 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4271 X0 sK3 sK2]
  have l1 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3]
    conv => enter [1]; rw [← l0 sK1 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54374_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54374 : Equation54374 G) : Equation4271 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54374 (sK0 ◇ sK0) X1 X0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
  have l16 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54374 sK0 X1 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ sK0 X1 X0 sK1 sK2 : G, (sK0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54374 (sK0 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0 X1 X0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h54374 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h54374 sK0 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l21 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ X0)]
  have l27 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0) ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 X0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l29 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54374 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
  have l32 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l4 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ X0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ X0) sK0]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l12 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l24 sK0 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ X0)]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l18 sK0 ((sK1 ◇ sK2) ◇ X0) (sK0 ◇ sK0)]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l35 sK0]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← h54374 sK0 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l40 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l42 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) X0]
  have l46 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54374 sK0 (sK0 ◇ sK0) X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l43 sK0 sK1 sK2 X0]
  have l47 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X0 (sK0 ◇ sK0)]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l50 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l49 sK0 X0 sK1 sK2]
  have l51 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l47 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l51 sK0]
  have l53 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [← l52 sK0]
  have l54 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l53 sK0]
  have l55 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [← l54 sK0]
  have l56 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l55 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l58 sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) sK0]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)]
  have l62 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54374 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l61 sK0 sK1 sK2]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [← l48 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l37 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l67 sK0 sK2 sK1]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l69 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l72 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l73 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [← l66 sK0 sK1 sK2]
  have l74 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l73 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l76 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK0 sK1 sK2]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
    conv => enter [1]; rw [← l76 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l56 sK0]
  intro x y z
  conv => enter [1]; rw [← l78 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54376 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54376 G := by
  have l0 : ∀ X0 sK0 sK3 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [← h4271 X0 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation4512_54376_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54376 : Equation54376 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54376 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h54376 sK0 X2 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54376 sK0 (sK1 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l2 sK0 X0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54376 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54376 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 X1 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X1 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l9 sK0 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) X1 sK0]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 X1 sK0 sK0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54376 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l11 sK0 (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h54376 X0 sK0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l15 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 (sK1 ◇ sK2) sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l17 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54377 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54377 G := by
  have l0 : ∀ X0 sK1 sK4 sK0 : G, (X0 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (X0 ◇ (sK4 ◇ sK0)) := by
    intro X0 sK1 sK4 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK4 sK0]
  have l1 : ∀ X0 sK3 sK4 sK0 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK4 ◇ sK0)) := by
    intro X0 sK3 sK4 sK0
    conv => enter [1]; rw [← h4271 X0 sK3 sK4]
    conv => enter [1]; rw [h4271 X0 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [← l0 sK2 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation4512_54377_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54377 : Equation54377 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h54377 X0 (sK0 ◇ sK0) sK0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54377 sK0 X0 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54377 sK0 sK0 sK0 X0 sK0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54377 sK0 X0 sK0 (sK1 ◇ sK2) sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54377 X0 sK0 sK0 (sK0 ◇ (X0 ◇ X0)) sK0]
    conv => enter [1, 2]; rw [← l8 sK0 X0 X0]
  have l10 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54377 X1 X2 X3 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h54377 X0 sK0 sK0 X3 sK0]
  have l11 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l10 X1 X2 X3 X1 sK0]
    conv => enter [1]; rw [l0 X1 X1 sK0]
  have l12 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l11 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l9 X1 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l14 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X0 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l12 X0 sK1 sK2 sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l16 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54383 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54383 G := by
  have l0 : ∀ X0 sK1 sK0 sK2 sK3 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l0 x w u x y z]

@[equational_result]
theorem Equation54383_implies_Equation4271 (G : Type*) [Magma G] (h54383 : Equation54383 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54383 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54383 X0 X3 X4 X0 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation54384 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54384 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 (sK0 ◇ sK3)]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l0 x w u y z]

@[equational_result]
theorem Equation54384_implies_Equation4271 (G : Type*) [Magma G] (h54384 : Equation54384 G) : Equation4271 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54384 X0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← h54384 X0 sK0 (sK1 ◇ sK2) X0 sK0]
  have l1 : ∀ X1 sK0 X2 X0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 X2 X0 sK1 sK2
    conv => enter [1]; rw [h54384 X1 sK0 X2 X0 sK0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK1 sK2]
  have l2 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l1 X1 sK0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [h54384 X1 sK0 X1 sK0 sK0]
  have l3 : ∀ X0 X2 X3 X1 sK0 sK1 sK2 : G, (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X2 X3 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54384 X0 X2 X3 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h54384 X0 (sK1 ◇ sK2) (X0 ◇ X2) X1 sK0]
  have l4 : ∀ X0 sK0 X2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X2 ◇ X3)) := by
    intro X0 sK0 X2 X3
    conv => enter [1]; rw [← l2 X0 X0 sK0 X0 X0]
    conv => enter [1]; rw [← l3 X0 X2 X3 X0 sK0 X0 X0]
  have l5 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54384 X0 sK0 (sK1 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [l4 X0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l6 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54386 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54386 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l0 x w u y z]

@[equational_result]
theorem Equation54386_implies_Equation4271 (G : Type*) [Magma G] (h54386 : Equation54386 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54386 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54386 X0 X3 X4 X0 X0]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 x y z x]

@[equational_result]
theorem Equation4271_implies_Equation54387 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54387 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l0 x w u y z]

@[equational_result]
theorem Equation54387_implies_Equation4271 (G : Type*) [Magma G] (h54387 : Equation54387 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54387 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54387 X0 X3 X4 X0 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation54388 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54388 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 sK4 sK5 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro X0 sK2 sK0 sK1 sK4 sK5
    conv => enter [1]; rw [← h4271 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4271 X0 sK4 sK5]
  intro x y z w u v
  conv => enter [1]; rw [← l0 x w u v y z]

@[equational_result]
theorem Equation54388_implies_Equation4271 (G : Type*) [Magma G] (h54388 : Equation54388 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54388 X0 X1 X2 X0 X0 X0]
    conv => enter [1]; rw [← h54388 X0 X3 X4 X0 X0 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation54312 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54312 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK0]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4512_54312_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54312 : Equation54312 G) : Equation4271 G := by
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
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54312 X0 X1 X2]
    conv => enter [1]; rw [← h54312 X0 X3 X4]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54312 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l8 X0 X0 X0 sK0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK1 sK2]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54313 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54313 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK0 sK1]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54313_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation4271 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54313 sK0 X0 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54313 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54313 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h54313 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK0]
  intro x y z
  conv => enter [1]; rw [← l16 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54315 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54315 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK1 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z x w]
  conv => enter [1]; rw [l0 x x w]

theorem Equation4512_54315_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54315 : Equation54315 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54315 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54315 X0 X4 X5 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54315 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l2 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 sK0 X2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 (sK1 ◇ sK2) X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54316 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54316 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54316_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54316 : Equation54316 G) : Equation4271 G := by
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
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54316 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54316 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK2)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54316 sK0 X0 X1]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54320 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54320 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK1 sK0]
  have l1 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x z x y]
  conv => enter [1]; rw [← l0 x x z]

theorem Equation4512_54320_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54320 : Equation54320 G) : Equation4271 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (X1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54320 sK0 (sK0 ◇ X0) X1]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 X1 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l5 sK0 X1 X0]
    conv => enter [1]; rw [← l5 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 X1]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← h54320 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X1 sK0]
    conv => enter [1]; rw [l10 sK0 X1 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l11 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l14 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54324 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54324 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  have l1 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK1]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w x]
  conv => enter [1]; rw [← l0 x x w]

theorem Equation4512_54324_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54324 : Equation54324 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54324 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54324 X0 X4 X5 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54324 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l2 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 sK0 X2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK0 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54317 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54317 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation54317_implies_Equation4271 (G : Type*) [Magma G] (h54317 : Equation54317 G) : Equation4271 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54317 X0 sK0 X1]
    conv => enter [1]; rw [← h54317 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54317 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54327 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54327 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4271 X0 sK2 sK2]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x w y z]
  conv => enter [1]; rw [← l0 x x w]

theorem Equation4512_54327_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54327 : Equation54327 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54327 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54327 X0 X4 X5 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54327 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l2 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 sK0 X2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 (sK1 ◇ sK2) X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54319 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54319 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 sK3 : G, (X0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← h4271 X0 sK2 sK0]
    conv => enter [1]; rw [h4271 X0 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK1 (sK2 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l0 sK1 sK2 sK0 sK1 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l1 x y w x]

theorem Equation4512_54319_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54319 : Equation54319 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54319 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [h54319 sK1 sK2 X1 X0]
  have l3 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l2 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X1 X0]
  have l6 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h54319 sK0 sK1 ((sK1 ◇ sK2) ◇ sK0) sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X1 sK0]
  have l7 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X1]
  have l8 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X1]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 1]; rw [← l8 sK0 sK1 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK2 X1]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 sK0 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l17 sK0 sK0]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0]
  have l21 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← h54319 sK0 sK0 (X0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54319 sK0 X0 X2 sK0]
  have l22 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X0 X2]
  have l23 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54319 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54319 X0 sK0 (sK1 ◇ sK2) sK0]
  have l24 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 sK0 X0 X2]
  have l25 : ∀ sK0 sK1 sK2 X0 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ X2)) := by
    intro sK0 sK1 sK2 X0 X2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK0 X0 X2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l23 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54325 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54325 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4271 X0 sK2 sK3]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x w y z]
  conv => enter [1]; rw [← l0 x x w y]

theorem Equation4512_54325_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54325 : Equation54325 G) : Equation4271 G := by
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
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← h54325 sK0 X0 X1 (sK1 ◇ sK2)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54325 sK0 X0 X1 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54325 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54325 sK0 sK0 X1 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1]; rw [h54325 (sK0 ◇ sK0) sK0 X1 X0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X1 X0]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ sK0)]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X1 sK0]
  have l16 : ∀ sK0 X1 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [← l15 sK0 X1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X1 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X1 sK1 sK2
    conv => enter [1]; rw [l16 sK0 X1 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l17 sK0 X1 sK1 sK2]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l18 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l18 sK0 sK0 sK0 X1]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 X1 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l4 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 sK0 X0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK0]
  intro x y z
  conv => enter [1]; rw [← l31 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54323 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54323 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4271 X0 sK2 sK3]
  have l1 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [← h4271 X0 sK0 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [← l0 x x z w]

theorem Equation4512_54323_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54323 : Equation54323 G) : Equation4271 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54323 X0 X1 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54323 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54323 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2]; rw [← h54323 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h54323 sK0 X1 X0 sK0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X1 X0]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l9 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54328 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54328 G := by
  have l0 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK2 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  have l1 : ∀ X0 sK1 sK0 sK3 sK4 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [← l0 x x w u]

theorem Equation4512_54328_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54328 : Equation54328 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54328 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54328 X0 X5 X6 X0 X0]
  have l2 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK0 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l3 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h54328 sK0 (sK0 ◇ sK0) X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X2]
  have l4 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 sK0 X0 X1 X2]
  have l5 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 sK0 X0 X1 X2]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 X0 X3 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X0 X3
    conv => enter [1]; rw [← l5 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 X3]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 X0]
  have l14 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 (sK1 ◇ sK2) X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l16 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54346 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54346 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4271 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4271 X0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4271 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4271 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 x z y]

theorem Equation4512_54346_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54346 : Equation54346 G) : Equation4271 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54346 sK0 X0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54346 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h54346 X3 (X0 ◇ X1) X2]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54346 sK0 X0 (sK1 ◇ sK2)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54346 sK0 X0 sK0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h54346 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54346 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l31 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l37 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [h54346 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0 sK0 sK0]
    conv => enter [1]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l46 sK0]
  have l48 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54346 sK0 X0 X1]
    conv => enter [1]; rw [h54346 sK0 X1 (sK0 ◇ sK0)]
  have l49 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l48 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l50 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l49 sK0 X0 X1]
    conv => enter [1]; rw [l6 sK0]
  have l51 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l50 sK0 X0 X1]
  have l52 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l21 sK0 sK0]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l51 sK0 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l55 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54363 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54363 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4271 X0 sK2 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK1 sK2]
    conv => enter [1]; rw [← h4271 sK1 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4271 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54363_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54363 : Equation54363 G) : Equation4271 G := by
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
  have l5 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54363 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54363 X0 X4 X5 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54363 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54363 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54363 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [l4 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1 sK2]
  have l15 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l7 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK0 X2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK0 sK0 (sK1 ◇ sK2)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 X1 sK1 sK2 X2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [l5 sK0 X0 X1 (sK1 ◇ sK2) X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) X2]
  have l19 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK0 sK1 sK2 X2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK0 (sK1 ◇ sK2) X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X2]
  have l22 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [← l20 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l24 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54366 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54366 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK2]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54366_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54366 : Equation54366 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54366 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54366 X0 X4 X5 X0]
  have l1 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h54366 sK0 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l2 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h54366 sK1 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l9 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK2 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK0 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54364 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54364 G := by
  have l0 : ∀ X0 sK1 sK3 sK2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK3]
    conv => enter [1]; rw [h4271 X0 sK2 (sK1 ◇ sK3)]
  have l1 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK1 sK1 sK3 sK2]
    conv => enter [1]; rw [l1 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 x w y z]

theorem Equation4512_54364_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54364 : Equation54364 G) : Equation4271 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54364 sK0 X0 X1 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54364 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54364 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54364 sK0 sK0 (sK1 ◇ sK2) X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h54364 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [l3 sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l20 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54349 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54349 G := by
  have l0 : ∀ X0 sK0 sK2 sK1 sK3 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK2 sK1 sK3
    conv => enter [1]; rw [← h4271 X0 sK0 sK2]
    conv => enter [1]; rw [h4271 X0 sK2 (sK1 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z x w]

theorem Equation4512_54349_implies_Equation4271 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54349 : Equation54349 G) : Equation4271 G := by
  have l0 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (X2 ◇ X1)) = (sK0 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [h54349 sK0 X2 X1 X0]
    conv => enter [1]; rw [h54349 sK0 X1 (sK0 ◇ X0) sK0]
  have l1 : ∀ sK0 X2 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X2 ◇ X1)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← h54349 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 X2 X1 sK0]
  have l2 : ∀ sK0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X2 ◇ X1)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 X2 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54349 sK0 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54349 sK0 sK0 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l2 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l11 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h54349 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h54349 sK0 X1 (sK0 ◇ sK0) (sK1 ◇ sK2)]
  have l12 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l11 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation4271_implies_Equation54367 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54367 G := by
  have l0 : ∀ X0 sK1 sK0 sK3 sK2 sK4 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK1 sK0 sK3 sK2 sK4
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK3 (sK2 ◇ sK4)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w x u]

@[equational_result]
theorem Equation54367_implies_Equation4271 (G : Type*) [Magma G] (h54367 : Equation54367 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X5 X6
    conv => enter [1]; rw [h54367 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54367 X0 X5 X6 X0 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation4271_implies_Equation54354 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54354 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK1 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h4271 X0 sK1 sK0]
    conv => enter [1]; rw [h4271 X0 sK2 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 x z y]

end Semigroup5
