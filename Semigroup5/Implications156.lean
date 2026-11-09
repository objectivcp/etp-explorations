import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_5055_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5055 : Equation5055 G) : Equation5 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h5055 (X0 ◇ (X0 ◇ (X2 ◇ X0))) X1 (X0 ◇ (X0 ◇ (X2 ◇ X0)))]
    conv => enter [1, 2, 2, 2]; rw [← h5055 X0 (X0 ◇ (X0 ◇ (X2 ◇ X0))) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X2 ◇ X0)) X0]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X0) X0]
  have l3 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l2 X0 X2 X0]
    conv => enter [1]; rw [← h5055 X0 X0 (X2 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h5055 X0 X1 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5059 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5059 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2]; rw [h5 (x ◇ (y ◇ (x ◇ x))) y]

theorem Equation4512_5059_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5059 : Equation5059 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5059 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5059 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5059 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5059 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ X0) sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5059 sK0 sK0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation5_implies_Equation5062 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5062 G := by
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
  conv => enter [1, 2]; rw [h5 (x ◇ (y ◇ (y ◇ x))) y]

theorem Equation4512_5062_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5062 : Equation5062 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5062 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK1 ◇ sK0) sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l9 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l12 sK1 sK0 X0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5062 (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 sK1 sK0]
  have l17 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) X0]
  have l18 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l20 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l18 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l22 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l20 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 (sK0 ◇ sK1) sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l15 sK0 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l26 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l26 sK1 sK0]
  have l30 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) X0]
  have l31 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l30 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) ((sK1 ◇ sK0) ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l25 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l34 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l31 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 X0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 ((sK1 ◇ sK0) ◇ sK1)]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1, 2]; rw [← l34 sK1 ((sK1 ◇ sK0) ◇ sK1) sK0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 ((sK1 ◇ sK0) ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l33 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)))]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 ((sK1 ◇ sK0) ◇ sK1) sK1]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 ((sK1 ◇ sK0) ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l42 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l48 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [l47 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l47 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l51 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l52 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l53 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l50 sK1 sK1]
    conv => enter [1]; rw [l27 sK1 sK1]
  have l54 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l53 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l55 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l52 sK1 (sK1 ◇ sK0) sK0]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5062 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l52 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l54 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [← l54 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l54 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1, 2]; rw [← l54 sK1 sK0]
  have l61 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l60 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l61 x y]

@[equational_result]
theorem Equation5_implies_Equation5065 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5065 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (x ◇ (y ◇ (z ◇ x))) y]

theorem Equation4512_5065_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5065 : Equation5065 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h5065 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X1 X1]
    conv => enter [1, 2, 2, 2]; rw [← h5065 X0 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h5065 X0 X1 (X2 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h5065 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l3 X0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X0 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 y x]

@[equational_result]
theorem Equation5_implies_Equation5069 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5069 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (x ◇ (z ◇ (x ◇ x))) y]

theorem Equation4512_5069_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5069 : Equation5069 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5069 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5069 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h5069 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5069 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h5069 X1 (X0 ◇ (X1 ◇ X1)) X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l6 X0 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l11 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l7 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 (X1 ◇ X1) (X1 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation5073 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5073 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (x ◇ (z ◇ (y ◇ x))) y]

theorem Equation4512_5073_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5073 : Equation5073 G) : Equation5 G := by
  have l0 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h5073 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (X0 ◇ sK1)]
  have l1 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h5073 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK1 sK1]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h5073 X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ X0)))]
    conv => enter [1]; rw [← h5073 X0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5077 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5077 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (x ◇ (z ◇ (z ◇ x))) y]

theorem Equation4512_5077_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5077 : Equation5077 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5077 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5077 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h5077 X0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [← h5077 X0 X1 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l5 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l7 : ∀ X0 X2 : G, (X0 ◇ X2) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X2
    conv => enter [1]; rw [l6 X0 X2 X0]
    conv => enter [1]; rw [l4 X0 ((X0 ◇ X0) ◇ X2)]
  have l8 : ∀ X0 X2 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X2
    conv => enter [1]; rw [l7 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l4 X0 X2]
    conv => enter [1, 2]; rw [← l8 X0 X2]
    conv => enter [1]; rw [l4 X0 X2]
  intro x y
  conv => enter [1]; rw [← l9 y x]

@[equational_result]
theorem Equation5_implies_Equation5081 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5081 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (x ◇ (z ◇ (w ◇ x))) y]

theorem Equation4512_5081_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5081 : Equation5081 G) : Equation5 G := by
  have l0 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h5081 (X0 ◇ (X2 ◇ (X3 ◇ X0))) X1 X0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h5081 X0 X0 X2 X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h5081 (X1 ◇ X0) (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h5081 X0 (X1 ◇ X0) X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l3 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l0 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ (X3 ◇ X0)) X0]
  have l4 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l3 X0 X2 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X3 ◇ X0) X0]
  have l5 : ∀ X0 X2 X3 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X0 := by
    intro X0 X2 X3
    conv => enter [1]; rw [l4 X0 X2 X3 X0]
    conv => enter [1]; rw [← h5081 X0 X0 X2 (X3 ◇ X0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l5 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 (X0 ◇ (X1 ◇ X2)) (X0 ◇ (X1 ◇ X2)) X2]
    conv => enter [1]; rw [← h5081 X2 (X0 ◇ (X1 ◇ X2)) X0 X1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation5_implies_Equation5086 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5086 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2, 2]; rw [h5 (x ◇ (x ◇ x)) y]

theorem Equation4512_5086_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5086 : Equation5086 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h5086 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h5086 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) X2]
    conv => enter [1, 1]; rw [← h5086 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X2]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l9 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l10 X0]
    conv => enter [1]; rw [← h5086 X0 X1]
  have l12 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l10 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h5086 X0 (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l15 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l12 X0]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l15 X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l11 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l16 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l17 X0]
    conv => enter [1]; rw [← h5086 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l17 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l17 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [l18 X0 X1]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation5_implies_Equation5089 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5089 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2, 2]; rw [h5 (x ◇ (y ◇ x)) y]

theorem Equation4512_5089_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5089 : Equation5089 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5089 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5089 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [h5089 X0 sK0]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X0)))) sK1]
    conv => enter [1]; rw [← h5089 X0 sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation5092 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5092 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2, 2]; rw [h5 (x ◇ (z ◇ x)) y]

theorem Equation4512_5092_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5092 : Equation5092 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h5092 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5092 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h5092 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l8 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l12 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h5092 X1 (X0 ◇ X1) X0]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l12 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation5_implies_Equation5096 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5096 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h5 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2, 2, 2]; rw [h5 (x ◇ x) y]

theorem Equation4512_5096_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5096 : Equation5096 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5096 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5096 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5096 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h5096 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 X0]
    conv => enter [1]; rw [← h5096 X0 X1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation5102 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5102 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h5 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2, 2, 2]; rw [h5 (z ◇ x) y]

theorem Equation4512_5102_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5102 : Equation5102 G) : Equation5 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5102 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5102 X2 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5106 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5106 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2, 2]; rw [h5 (z ◇ (x ◇ x)) y]

theorem Equation4512_5106_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5106 : Equation5106 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h5106 (X0 ◇ X0) X1 X1]
    conv => enter [1, 2]; rw [← h5106 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1]; rw [← h5106 X1 X2 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l2 (X0 ◇ (X1 ◇ X1)) X2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ (X1 ◇ X1)) X0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l3 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l2 X1 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l2 X1 X1 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X1 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l2 X1 X1 X1]
    conv => enter [1]; rw [l9 X1 X1]
  have l11 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5106 sK0 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 sK0 sK1]
  have l12 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l2 (sK1 ◇ sK0) X0 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l2 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation5110 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5110 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2, 2]; rw [h5 (z ◇ (y ◇ x)) y]

theorem Equation4512_5110_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5110 : Equation5110 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h5110 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h5110 (X0 ◇ (sK1 ◇ sK0)) sK1 sK1]
    conv => enter [1, 2, 2]; rw [← h5110 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h5110 (sK1 ◇ sK0) sK1 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation5114 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5114 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2, 2]; rw [h5 (z ◇ (z ◇ x)) y]

theorem Equation4512_5114_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5114 : Equation5114 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h5114 X0 X2 X1]
    conv => enter [1]; rw [← h5114 (X1 ◇ (X1 ◇ X0)) X2 X2]
  have l1 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1, 2]; rw [h5114 sK0 X1 sK1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ sK0 X1 X0 sK1 : G, sK0 = (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h5114 sK0 X1 sK1]
    conv => enter [1, 2]; rw [l0 X1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 X1 X0 X0]
  have l4 : ∀ sK0 X1 X2 X0 : G, sK0 = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h5114 sK0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l3 X2 sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
  have l7 : ∀ sK0 X1 X2 sK1 : G, sK0 = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [l4 sK0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [l3 sK0 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5114 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation5118 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5118 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2, 2]; rw [h5 (z ◇ (w ◇ x)) y]

theorem Equation4512_5118_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5118 : Equation5118 G) : Equation5 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5118 X3 X4 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 : G, (X2 ◇ X3) = X3 := by
    intro X2 X3
    conv => enter [1, 2]; rw [h5118 X3 X2 X2 X2]
    conv => enter [1]; rw [l0 X2 X2 X2 X2 X3]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5123 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5123 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (x ◇ (x ◇ x))) y]

theorem Equation4512_5123_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5123 : Equation5123 G) : Equation5 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h5123 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h5123 (X0 ◇ (X0 ◇ X0)) X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h5123 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← h5123 X0 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

@[equational_result]
theorem Equation5_implies_Equation5127 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5127 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (x ◇ (y ◇ x))) y]

theorem Equation4512_5127_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5127 : Equation5127 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5127 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5127 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5131 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5131 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (x ◇ (z ◇ x))) y]

theorem Equation4512_5131_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5131 : Equation5131 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5131 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X0)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h5131 (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h5131 X0 X2 X3]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h5131 (X2 ◇ (X0 ◇ (X2 ◇ X0))) X1 (X2 ◇ (X0 ◇ (X2 ◇ X0)))]
    conv => enter [1, 2, 2, 2]; rw [← h5131 X0 (X2 ◇ (X0 ◇ (X2 ◇ X0))) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ (X2 ◇ X0)) X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X0))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X3 ◇ (X0 ◇ (X3 ◇ X0))) X0]
  have l5 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X0) X0]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l4 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 (X0 ◇ (X3 ◇ X0)) X0]
  have l8 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l5 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X0 X0]
  have l10 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X0))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l7 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h5131 X0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l10 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X3 X0 X0]
  have l13 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l12 X2 X3 X0 X1]
    conv => enter [1, 2, 2]; rw [← l9 X3 X0 X2]
  have l14 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := by
    intro X2 X3 X0
    conv => enter [1]; rw [l13 X2 X3 X0 X2]
    conv => enter [1]; rw [← h5131 X0 X2 X3]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l11 sK0 X0]
  have l16 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [← l15 sK1 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5131 X1 (sK1 ◇ sK0) X0]
  have l17 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ X1) = X1 := by
    intro sK1 sK0 X1
    conv => enter [1, 2]; rw [← l14 sK1 sK1 X1]
    conv => enter [1]; rw [l16 sK1 sK0 sK1 X1]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK1 sK0 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation5_implies_Equation5135 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5135 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (x ◇ (w ◇ x))) y]

theorem Equation4512_5135_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5135 : Equation5135 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5135 (sK0 ◇ X0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
    conv => enter [1]; rw [← h5135 X2 X4 (X0 ◇ X1) X3]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5135 X0 X1 (X2 ◇ X0) X2]
    conv => enter [1]; rw [← h5135 (X2 ◇ X0) X1 X1 X0]
  have l3 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5140 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5140 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (y ◇ (x ◇ x))) y]

theorem Equation4512_5140_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5140 : Equation5140 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5140 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5140 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5140 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h5140 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l7 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5140 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation5144 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5144 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (y ◇ (y ◇ x))) y]

theorem Equation4512_5144_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5144 : Equation5144 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5144 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5144 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5148 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5148 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (y ◇ (z ◇ x))) y]

theorem Equation4512_5148_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5148 : Equation5148 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← h5148 X0 sK1 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l0 sK1 sK0 X0]
  have l2 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l1 sK1 sK0 ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0))))]
    conv => enter [1, 2, 2]; rw [← h5148 X0 (sK1 ◇ sK0) X1]
  have l3 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ X0) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1, 2]; rw [h5148 X0 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [l1 sK1 sK0 (X1 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ X0)))]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l3 sK1 X0 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK1 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5148 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5148 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5148 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0 (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation5152 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5152 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (y ◇ (w ◇ x))) y]

theorem Equation4512_5152_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5152 : Equation5152 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5152 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5152 X2 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5157 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5157 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (z ◇ (x ◇ x))) y]

theorem Equation4512_5157_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5157 : Equation5157 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h5157 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X1 (X2 ◇ (X2 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2, 2, 2]; rw [← h5157 X0 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X2]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5157 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5157 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) X3]
    conv => enter [1, 1]; rw [← h5157 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X3]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ (X0 ◇ X0)) X0]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ (X0 ◇ X0)) X3]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X0) X0]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X3]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
  have l12 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := by
    intro X2 X0
    conv => enter [1]; rw [l11 X2 X0 X2]
    conv => enter [1]; rw [← h5157 X0 X2 X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l4 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5157 X0 X1 (X0 ◇ X0)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← h5157 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l12 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l15 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 (X1 ◇ X1) X0 X1]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l16 X1]
    conv => enter [1]; rw [l19 X0 X1]
  intro x y
  conv => enter [1]; rw [← l20 y x]

@[equational_result]
theorem Equation5_implies_Equation5161 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5161 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (z ◇ (y ◇ x))) y]

theorem Equation4512_5161_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5161 : Equation5161 G) : Equation5 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h5161 (X0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h5161 sK0 sK1 X0]
  have l1 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h5161 (X0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5161 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l1 X0 sK0 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5161 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5161 sK0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation5_implies_Equation5165 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5165 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ (z ◇ (z ◇ x))) y]

theorem Equation4512_5165_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5165 : Equation5165 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h5165 X0 X1 X1]
    conv => enter [1]; rw [← h5165 (X1 ◇ (X1 ◇ X0)) X2 X1]
  have l1 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1, 2]; rw [h5165 sK0 X1 sK1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [l0 X0 X1 X3]
    conv => enter [1]; rw [← h5165 X1 X2 X3]
  have l3 : ∀ sK0 X1 X0 sK1 : G, sK0 = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h5165 sK0 X1 sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [← l2 sK1 X1 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l1 X1 sK0 sK1 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5165 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation5_implies_Equation5169 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5169 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (z ◇ (w ◇ x))) y]

theorem Equation4512_5169_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5169 : Equation5169 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5169 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5169 X2 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5174 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5174 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (w ◇ (x ◇ x))) y]

theorem Equation4512_5174_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5174 : Equation5174 G) : Equation5 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [← h5174 X3 X4 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5174 X0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5174 (X0 ◇ X0) X1 X1 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [l1 X0 (X1 ◇ (X2 ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h5174 X3 (X1 ◇ (X2 ◇ (X3 ◇ X3))) X1 X2]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ X3)) (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 (X3 ◇ X3) (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 X3 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l7 : ∀ X1 X2 X3 : G, (X1 ◇ (X2 ◇ X3)) = X3 := by
    intro X1 X2 X3
    conv => enter [1, 2, 2]; rw [← l0 X3 X1 X1 X2 X3]
    conv => enter [1]; rw [l6 X1 X2 X3 X1]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5174 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l10 : ∀ sK0 X1 X2 sK1 : G, sK0 = (X1 ◇ (X2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [l9 sK0 sK0 X1 X2 sK1]
    conv => enter [1]; rw [l7 sK0 sK0 (X1 ◇ (X2 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK0 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation5_implies_Equation5179 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5179 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (w ◇ (y ◇ x))) y]

theorem Equation4512_5179_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5179 : Equation5179 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5179 sK0 sK1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5179 sK0 sK1 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5184 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5184 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (w ◇ (z ◇ x))) y]

theorem Equation4512_5184_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5184 : Equation5184 G) : Equation5 G := by
  have l0 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X4 X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5184 X3 X4 X2 (X0 ◇ X1)]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [← h5184 X3 X4 (X0 ◇ X1) X2]
  have l2 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l1 X4 X0 X1 X2 X3]
  have l3 : ∀ X1 X3 : G, (X1 ◇ X3) = X3 := by
    intro X1 X3
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X3]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X3]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5189 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5189 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1, 2]; rw [h5 (z ◇ (w ◇ (w ◇ x))) y]

theorem Equation4512_5189_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5189 : Equation5189 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5189 X0 X1 X2 X2]
    conv => enter [1]; rw [← h5189 (X2 ◇ X0) X1 X1 X2]
  have l1 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5189 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X2 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5189 (sK1 ◇ sK0) X0 X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5194 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5194 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK4]
    conv => enter [1]; rw [h5 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]
  conv => enter [1, 2]; rw [h5 (z ◇ (w ◇ (u ◇ x))) y]

theorem Equation4512_5194_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5194 : Equation5194 G) : Equation5 G := by
  have l0 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5194 X4 X5 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X3 X4 : G, (X3 ◇ X4) = X4 := by
    intro X3 X4
    conv => enter [1, 2]; rw [h5194 X4 X3 X3 X3 X3]
    conv => enter [1]; rw [l0 X3 X3 X3 X3 X3 X4]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5200 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5200 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2, 2]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_5200_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5200 : Equation5200 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5200 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5200 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5204 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5204 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_5204_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5204 : Equation5204 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5204 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5204 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5208 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5208 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_5208_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5208 : Equation5208 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5208 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5208 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5208 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5212 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5212 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (x ◇ (w ◇ x)))) y]

theorem Equation4512_5212_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5212 : Equation5212 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5212 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5212 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5217 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5217 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_5217_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5217 : Equation5217 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = (sK1 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h5217 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation5221 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5221 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_5221_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5221 : Equation5221 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5221 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5221 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5225 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5225 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_5225_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5225 : Equation5225 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5225 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (sK1 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h5225 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l4 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h5225 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l5 sK0 X0]
  have l7 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((sK1 ◇ sK0) ◇ (X0 ◇ X1))]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0 X0]
    conv => enter [1]; rw [← h5225 X1 (X0 ◇ X0) X0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5225 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [l10 X0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)))]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l10 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation5229 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5229 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (y ◇ (w ◇ x)))) y]

theorem Equation4512_5229_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5229 : Equation5229 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5229 (sK0 ◇ X0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X0))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5229 (X0 ◇ (X1 ◇ (X3 ◇ X0))) X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h5229 X0 X1 X0 X3]
  have l2 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))))) = X2 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X2)))]
    conv => enter [1]; rw [← h5229 X2 X3 (X0 ◇ X1) X4]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X0)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X3 ◇ X0)) X0]
  have l4 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X0))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X3 ◇ X0) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK0 X0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = X0 := by
    intro X0 X1 X3
    conv => enter [1]; rw [l5 X0 X1 X3 X0]
    conv => enter [1]; rw [← h5229 X0 X1 X0 (X3 ◇ X0)]
  have l8 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ X1)))) = X1 := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ X1))))]
    conv => enter [1]; rw [← h5229 X1 sK0 X0 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]

@[equational_result]
theorem Equation5_implies_Equation5234 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5234 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_5234_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5234 : Equation5234 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5234 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5234 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5238 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5238 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_5238_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5238 : Equation5238 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h5238 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5238 X0 X2 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5238 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5238 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h5238 X0 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h5238 (X0 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l13 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l2 X0]
    conv => enter [1]; rw [l6 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l5 X0 X0 X1]
  have l15 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0 X0]
    conv => enter [1]; rw [l13 X0]
  have l16 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l15 X0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l15 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l16 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l16 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5238 X1 X0 (X0 ◇ X1)]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l20 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l21 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l14 X1 X0]
    conv => enter [1]; rw [l22 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l16 X1]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h5238 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l18 sK1 sK0]
  have l26 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [l24 (sK1 ◇ sK0) (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))))]
  have l27 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 X0 sK1]
    conv => enter [1]; rw [l24 X0 (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l27 sK0 X0 sK1]
    conv => enter [1]; rw [l24 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l29 x y]

@[equational_result]
theorem Equation5_implies_Equation5242 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5242 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_5242_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5242 : Equation5242 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5242 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5242 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5242 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5246 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5246 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_5246_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5246 : Equation5246 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5246 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5246 X0 X0 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0 (X1 ◇ X0) X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5251 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5251 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (w ◇ (x ◇ x)))) y]

theorem Equation4512_5251_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5251 : Equation5251 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5251 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5251 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5256 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5256 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (w ◇ (y ◇ x)))) y]

theorem Equation4512_5256_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5256 : Equation5256 G) : Equation5 G := by
  have l0 : ∀ X2 X4 X3 X0 X1 : G, (X2 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X4 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5256 X3 X2 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5256 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 (X1 ◇ X0) X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5261 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5261 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (w ◇ (z ◇ x)))) y]

theorem Equation4512_5261_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5261 : Equation5261 G) : Equation5 G := by
  have l0 : ∀ sK0 X1 sK1 X0 : G, sK0 = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h5261 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5261 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5261 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0 X1]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK0 sK1 X0]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5266 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5266 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (w ◇ (w ◇ x)))) y]

theorem Equation4512_5266_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5266 : Equation5266 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5266 X0 X1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5266 (X0 ◇ X0) X1 X1 X0]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5266 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5266 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0 X1]
  have l3 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5266 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l3 sK0 sK0 X1 sK1]
    conv => enter [1]; rw [l2 sK0 (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation5271 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5271 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ (w ◇ (u ◇ x)))) y]

theorem Equation4512_5271_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5271 : Equation5271 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 X5 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4 X5
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5271 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5271 X0 X1 (X1 ◇ X0) X1 X1]
    conv => enter [1]; rw [l0 X1 X1 (X1 ◇ X0) X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5277 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5277 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_5277_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5277 : Equation5277 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h5277 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5277 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5281 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5281 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_5281_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5281 : Equation5281 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h5281 (X0 ◇ (X1 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h5281 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h5281 X3 X2 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) X3]
    conv => enter [1, 1]; rw [← h5281 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 X3]
  have l7 : ∀ sK0 X0 sK1 X1 : G, ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ X0) sK1 X1]
  have l8 : ∀ X2 X3 X1 X0 : G, (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) = ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) X2 X3]
    conv => enter [1, 2]; rw [← h5281 X0 X2 X1]
  have l9 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X2 X3 X1 : G, (X0 ◇ X2) = (X2 ◇ (X3 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h5281 (X0 ◇ X2) X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X2 X0 X1]
  have l11 : ∀ X0 X2 X3 X1 : G, (X0 ◇ X2) = (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l10 X0 X2 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 (X0 ◇ (X1 ◇ X2))]
  have l12 : ∀ X2 X3 X1 X0 : G, (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) = (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0)) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [l8 X2 X3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X2 ◇ X0))) X0]
  have l13 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) = (sK1 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l7 sK0 X0 sK1 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 (X1 ◇ X2) X2 X0]
    conv => enter [1]; rw [← l11 X0 X2 X0 X1]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ (X0 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [← l12 X2 X3 X1 X0]
  have l16 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ X0)) = (sK1 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l9 X0 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0 X0 sK1 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X1 X0]
  have l18 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l14 sK1 sK1 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l16 X0 sK0 sK1 sK1]
  have l19 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l14 X0 X0 X0]
    conv => enter [1]; rw [l17 X0 X0]
  have l20 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1]; rw [l14 X0 sK0 X0]
  have l21 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [l19 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [← l14 sK1 sK1 X0]
    conv => enter [1]; rw [l21 sK1 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l22 y x]

@[equational_result]
theorem Equation5_implies_Equation5285 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5285 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_5285_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5285 : Equation5285 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5285 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5285 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5285 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5285 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5285 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5285 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation5289 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5289 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (x ◇ (w ◇ x)))) y]

theorem Equation4512_5289_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5289 : Equation5289 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))))) = X3 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X3)))]
    conv => enter [1]; rw [← h5289 X3 X2 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5289 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X4 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 (X1 ◇ X0) X1 X1 X0 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0) X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5294 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5294 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_5294_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5294 : Equation5294 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5294 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5294 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h5294 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h5294 (X0 ◇ X0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l5 X0 (X0 ◇ X0)]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← h5294 X1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation5298 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5298 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2, 2]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_5298_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5298 : Equation5298 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h5298 (X1 ◇ (X1 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h5298 X0 X1 X1]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h5298 X3 X2 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5298 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X2 ((X1 ◇ X2) ◇ X0) (X1 ◇ X2)]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l0 X2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X1 X1 X0]
    conv => enter [1]; rw [l5 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

@[equational_result]
theorem Equation5_implies_Equation5302 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5302 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_5302_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5302 : Equation5302 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h5302 (X1 ◇ (X1 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5302 X0 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h5302 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h5302 X0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [l3 sK1 sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [l3 sK1 sK0 X0]
  have l6 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1)))) = X1 := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2]; rw [← l5 sK1 sK0 (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1)))]
    conv => enter [1]; rw [← h5302 X1 X0 (sK1 ◇ sK0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X0 X0 X1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5302 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l3 sK1 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation5_implies_Equation5306 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5306 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (y ◇ (w ◇ x)))) y]

theorem Equation4512_5306_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5306 : Equation5306 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5306 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5306 X2 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5311 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5311 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_5311_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5311 : Equation5311 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5311 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5311 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5311 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h5311 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5311 X0 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5_implies_Equation5315 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5315 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_5315_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5315 : Equation5315 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h5315 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5315 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X0 X1 X3]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l5 : ∀ X2 X0 : G, (X2 ◇ X0) = X0 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l3 X2 X2 X2 X0]
    conv => enter [1]; rw [l4 X2 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

@[equational_result]
theorem Equation5_implies_Equation5319 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5319 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_5319_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5319 : Equation5319 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h5319 (X2 ◇ (X2 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5319 X0 X2 X2]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h5319 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h5319 X0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5319 ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [l2 sK1 sK0 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5319 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 (sK1 ◇ sK0) sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h5319 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK1 ◇ sK0) sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5319 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5319 sK0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation5323 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5323 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_5323_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5323 : Equation5323 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5323 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5323 X2 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5328 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5328 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (w ◇ (x ◇ x)))) y]

theorem Equation4512_5328_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5328 : Equation5328 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X4 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h5328 X4 X2 (X0 ◇ X1) X3]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5328 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X4 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5333 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5333 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (w ◇ (y ◇ x)))) y]

theorem Equation4512_5333_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5333 : Equation5333 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5333 X0 X2 X1 X1]
    conv => enter [1]; rw [← h5333 (X2 ◇ X0) X1 X2 X2]
  have l1 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5333 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5333 (sK1 ◇ sK0) sK1 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5338 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5338 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (w ◇ (z ◇ x)))) y]

theorem Equation4512_5338_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5338 : Equation5338 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5338 sK0 sK1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5338 sK0 sK1 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5343 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5343 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (w ◇ (w ◇ x)))) y]

theorem Equation4512_5343_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5343 : Equation5343 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5343 X4 X2 (X0 ◇ X1) X3]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5343 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ (X4 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X4 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5348 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5348 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK4 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK4 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK3 sK1 sK0 : G, sK2 = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4 sK3]
  intro x y z w u
  conv => enter [1]; rw [l2 x z y w u]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ (w ◇ (u ◇ x)))) y]

theorem Equation4512_5348_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5348 : Equation5348 G) : Equation5 G := by
  have l0 : ∀ X4 X5 X0 X1 X2 X3 : G, (X4 ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X4 X5 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5348 X3 X4 X5 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 : G, (X2 ◇ X3) = X3 := by
    intro X2 X3
    conv => enter [1, 2]; rw [h5348 X3 X2 X2 X2 X2]
    conv => enter [1]; rw [l0 X2 X2 X2 X2 X2 X3]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5354 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5354 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_5354_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5354 : Equation5354 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5354 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5354 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5358 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5358 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_5358_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5358 : Equation5358 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (X0 ◇ (sK1 ◇ X0)))]
    conv => enter [1]; rw [← h5358 X0 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5358 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5358 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← h5358 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
    conv => enter [1]; rw [← h5358 X0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5_implies_Equation5362 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5362 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_5362_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5362 : Equation5362 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5362 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5362 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5362 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5366 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5366 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (x ◇ (w ◇ x)))) y]

theorem Equation4512_5366_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5366 : Equation5366 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5366 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5366 X0 (X1 ◇ X0) (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) (X1 ◇ X0) X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5371 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5371 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_5371_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5371 : Equation5371 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5371 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5371 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5371 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5371 X1 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

@[equational_result]
theorem Equation5_implies_Equation5375 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5375 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_5375_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5375 : Equation5375 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5375 (sK1 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h5375 sK0 sK1 X0]
  have l1 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ sK0) = (sK1 ◇ (X1 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h5375 (sK1 ◇ sK0) sK1 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 sK1 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (sK1 ◇ (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l1 sK1 sK0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK1 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5375 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation5379 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5379 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_5379_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5379 : Equation5379 G) : Equation5 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h5379 (X2 ◇ (X1 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5379 X0 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h5379 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))]
    conv => enter [1]; rw [← h5379 X0 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5379 ((sK1 ◇ sK0) ◇ X0) sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l3 sK0 sK1 X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l7 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1)))) = X1 := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X1))]
    conv => enter [1]; rw [← h5379 X1 X0 (sK1 ◇ sK0)]
  have l8 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) = X1 := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2]; rw [← l6 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X1))]
    conv => enter [1]; rw [l7 X0 sK1 sK0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X0 X0 X1]
    conv => enter [1]; rw [l8 X0 X0 X0 X1]
  have l10 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [← l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) X0]
  intro x y
  conv => enter [1]; rw [← l11 y x]

@[equational_result]
theorem Equation5_implies_Equation5383 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5383 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (y ◇ (w ◇ x)))) y]

theorem Equation4512_5383_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5383 : Equation5383 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5383 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5383 X2 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

end Semigroup5
