import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation151_212_221_255_implies_Equation66 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0 X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h221 X0 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ (X0 ◇ X2)) X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l9 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2, 1]; rw [l11 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l11 X1]
  intro x y
  conv => enter [1]; rw [← l13 y x]
  conv => enter [1, 2, 2]; rw [← l11 y]

theorem Equation151_212_221_255_implies_Equation115 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0 X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h221 X0 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ (X0 ◇ X2)) X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l9 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2, 1]; rw [l11 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l11 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l13 y (x ◇ x)]

theorem Equation151_212_221_255_implies_Equation72 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0 X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X0) ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h221 X0 X2]
    conv => enter [1]; rw [l8 X0 (X2 ◇ (X0 ◇ X2)) X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [l8 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l9 X0 X0 X0]
    conv => enter [1]; rw [← l10 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 1]; rw [← l12 X0]
    conv => enter [1, 2, 1, 1]; rw [← l12 X0]
    conv => enter [1, 1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x]
  conv => enter [1]; rw [← l15 y (x ◇ x)]

theorem Equation47_105_127_151_implies_Equation14 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0 X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X0)) X1]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h105 X0 X2]
    conv => enter [1]; rw [l9 X0 ((X2 ◇ X0) ◇ X2) X1]
  have l11 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l9 X1 (X2 ◇ X0) (X2 ◇ X2)]
    conv => enter [1, 1]; rw [l0 X2 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) X1]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← l12 X0 X0]
  have l14 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l13 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [l14 X1]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [← l14 X0]
    conv => enter [1, 1, 2, 2]; rw [← l14 X0]
    conv => enter [1, 2, 1]; rw [← l14 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [← l14 X2]
    conv => enter [1]; rw [← l11 X1 X2 X0]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 (X1 ◇ X0)]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l14 X1]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l18 X1 X0]
  have l21 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l17 X2 X0 X2]
    conv => enter [1]; rw [l19 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l20 x y]
  conv => enter [1]; rw [l21 (x ◇ y) y]

theorem Equation47_105_127_151_implies_Equation332 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0 X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h105 X0 X2]
    conv => enter [1]; rw [l7 X0 ((X2 ◇ X0) ◇ X2) X1]
  have l9 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 (X2 ◇ X0) (X2 ◇ X2)]
    conv => enter [1, 1]; rw [l0 X2 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) X1]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l10 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [l12 X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [← l12 X2]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l12 X1]
  have l16 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l14 X2 X0 X2]
    conv => enter [1]; rw [l15 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [l16 x y]
  conv => enter [1, 2]; rw [← l12 x]

theorem Equation47_105_127_151_implies_Equation66 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0 X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h105 X0 X2]
    conv => enter [1]; rw [l7 X0 ((X2 ◇ X0) ◇ X2) X1]
  have l9 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 (X2 ◇ X0) (X2 ◇ X2)]
    conv => enter [1, 1]; rw [l0 X2 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) X1]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l10 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [l12 X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [← l12 X2]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l12 X1]
  have l16 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l14 X2 X0 X2]
    conv => enter [1]; rw [l15 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l15 y x]
  conv => enter [1, 1, 1]; rw [← l12 y]
  conv => enter [1, 1]; rw [l16 (y ◇ y) x]
  conv => enter [1]; rw [l16 (x ◇ (y ◇ y)) y]

theorem Equation47_105_127_151_implies_Equation115 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0 X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X0)) X1]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h105 X0 X2]
    conv => enter [1]; rw [l9 X0 ((X2 ◇ X0) ◇ X2) X1]
  have l11 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l9 X1 (X2 ◇ X0) (X2 ◇ X2)]
    conv => enter [1, 1]; rw [l0 X2 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) X1]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← l12 X0 X0]
  have l14 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l13 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [l14 X1]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [← l14 X0]
    conv => enter [1, 1, 2, 2]; rw [← l14 X0]
    conv => enter [1, 2, 1]; rw [← l14 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [← l14 X2]
    conv => enter [1]; rw [← l11 X1 X2 X0]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 (X1 ◇ X0)]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l14 X1]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l18 X1 X0]
  have l21 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l17 X2 X0 X2]
    conv => enter [1]; rw [l19 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1]; rw [← l20 (x ◇ x) y]
  conv => enter [1]; rw [l21 ((x ◇ x) ◇ y) y]

theorem Equation47_105_127_151_implies_Equation72 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X0 X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h105 X0 X2]
    conv => enter [1]; rw [l7 X0 ((X2 ◇ X0) ◇ X2) X1]
  have l9 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 (X2 ◇ X0) (X2 ◇ X2)]
    conv => enter [1, 1]; rw [l0 X2 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0) X1]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l10 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [l12 X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [← l12 X2]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l12 X1]
  have l16 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [l14 X2 X0 X2]
    conv => enter [1]; rw [l15 X2 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l12 x]
  conv => enter [1]; rw [← l15 y (x ◇ x)]
  conv => enter [1]; rw [l16 (y ◇ (x ◇ x)) y]

theorem Equation151_211_implies_Equation25 (G : Type*) [Magma G] (h151 : Equation151 G) (h211 : Equation211 G) : Equation25 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h211 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation107_151_implies_Equation10 (G : Type*) [Magma G] (h107 : Equation107 G) (h151 : Equation151 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h107 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation151_209_264_implies_Equation3 (G : Type*) [Magma G] (h151 : Equation151 G) (h209 : Equation209 G) (h264 : Equation264 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h209 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 1]; rw [← l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l0 X0 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h209 X0 X0]
    conv => enter [1]; rw [l7 X0]
  intro x
  conv => enter [1]; rw [← l8 x]

theorem Equation75_117_151_implies_Equation3 (G : Type*) [Magma G] (h75 : Equation75 G) (h117 : Equation117 G) (h151 : Equation151 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h117 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 1]; rw [← l1 X0 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← l5 X0]
  have l7 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l0 X0 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h117 X0 X0]
    conv => enter [1]; rw [l7 X0]
  intro x
  conv => enter [1]; rw [← l8 x]

theorem Equation151_205_264_implies_Equation9 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h264 : Equation264 G) : Equation9 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l1 X0 X2]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X1) X1 X2]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [← l3 X0 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← h264 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l2 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation75_104_151_implies_Equation28 (G : Type*) [Magma G] (h75 : Equation75 G) (h104 : Equation104 G) (h151 : Equation151 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l1 X2 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [← l3 X0 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [l2 X0 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation151_205_221_implies_Equation255 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h221 : Equation221 G) : Equation255 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h205 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h221 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l0 X0]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← l3 X0]
    conv => enter [1]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [← l4 x]

theorem Equation104_105_151_implies_Equation47 (G : Type*) [Magma G] (h104 : Equation104 G) (h105 : Equation105 G) (h151 : Equation151 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h105 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← l0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← l3 X0]
    conv => enter [1]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [← l4 x]

theorem Equation151_205_212_255_implies_Equation258 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation258 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X0 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l12 (x ◇ x) y]

theorem Equation151_205_212_255_implies_Equation261 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation261 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) (X1 ◇ X1) X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 X0 X0 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [l12 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l15 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l9 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l13 x y]
  conv => enter [1, 1]; rw [l16 x y]

theorem Equation151_205_212_255_implies_Equation26 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation26 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X0 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 x y]

theorem Equation151_205_212_255_implies_Equation362 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation362 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X0 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l11 x]
  conv => enter [1]; rw [← l12 x y]

theorem Equation151_205_212_255_implies_Equation9 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 X0 X0 (X0 ◇ X0)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l11 X0]
  intro x y
  conv => enter [1]; rw [← l13 x y]

theorem Equation151_205_212_255_implies_Equation101 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation101 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
    conv => enter [1, 1, 2]; rw [← h151 X0]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) (X1 ◇ X1) X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X2)]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l8 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 X0 X0 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l12 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l9 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l14 x y]
  conv => enter [1, 2]; rw [l15 x y]

theorem Equation47_104_127_151_implies_Equation72 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation72 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l12 y (x ◇ x)]

theorem Equation47_104_127_151_implies_Equation65 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation65 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l6 (X1 ◇ X1) (X1 ◇ X0) X2]
  have l10 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 (X0 ◇ X0) X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [l12 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l15 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← l9 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l13 y x]
  conv => enter [1, 2]; rw [l16 y x]

theorem Equation47_104_127_151_implies_Equation16 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation16 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation47_104_127_151_implies_Equation315 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation315 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x]
  conv => enter [1]; rw [← l12 y x]

theorem Equation47_104_127_151_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X0) X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l11 X0]
  intro x y
  conv => enter [1]; rw [← l13 y x]

theorem Equation47_104_127_151_implies_Equation208 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation208 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l6 (X1 ◇ X1) (X1 ◇ X0) X2]
  have l10 : ∀ X2 X0 X1 : G, (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l2 (X2 ◇ X0) X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 (X0 ◇ X0) X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l12 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l14 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← l9 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l14 y x]
  conv => enter [1, 1]; rw [l15 y x]

theorem Equation167_273_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h273 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation53_167_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [← h53 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation167_264_implies_Equation3 (G : Type*) [Magma G] (h167 : Equation167 G) (h264 : Equation264 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h264 X0 X1]
    conv => enter [1, 2]; rw [← h264 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h264 X0 X0]
    conv => enter [1]; rw [← l1 X0 X0]
  have l3 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← l2 X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h264 X0 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation75_167_implies_Equation3 (G : Type*) [Magma G] (h75 : Equation75 G) (h167 : Equation167 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h75 X0 X1]
    conv => enter [1, 1]; rw [← h75 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [h75 X0 X0]
    conv => enter [1]; rw [← l1 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation167_260_implies_Equation3 (G : Type*) [Magma G] (h167 : Equation167 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h260 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation49_167_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h167 : Equation167 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h49 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation167_231_283_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h231 : Equation231 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h283 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h231 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation56_108_167_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h108 : Equation108 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h56 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h108 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation167_212_255_implies_Equation73 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l6 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l7 x y]
  conv => enter [1]; rw [l8 (x ◇ y) y]

theorem Equation167_212_255_implies_Equation125 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l7 X1]
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l7 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l7 (X0 ◇ X1)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1, 2]; rw [l11 x y]

theorem Equation167_212_255_implies_Equation335 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l6 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation167_212_255_implies_Equation258 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation258 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l6 (x ◇ x) y]

theorem Equation167_212_255_implies_Equation65 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation65 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l6 X1]
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l6 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation167_212_255_implies_Equation26 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation26 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation167_212_255_implies_Equation362 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation362 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x]
  conv => enter [1]; rw [← l6 x y]

theorem Equation167_212_255_implies_Equation117 (G : Type*) [Magma G] (h167 : Equation167 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation117 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l6 (X0 ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]
  conv => enter [1]; rw [l8 (x ◇ y) y]
  conv => enter [1, 2]; rw [l9 y x]

theorem Equation47_127_167_implies_Equation118 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l5 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l6 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1, 2]; rw [l8 y x]

theorem Equation47_127_167_implies_Equation222 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l6 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l7 X1]
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l7 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l7 (X1 ◇ X0)]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l8 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]
  conv => enter [1, 1]; rw [l11 x y]

theorem Equation47_127_167_implies_Equation384 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l5 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l6 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation47_127_167_implies_Equation72 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation47_127_167_implies_Equation261 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation261 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l5 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l6 X1]
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l6 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation47_127_167_implies_Equation16 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation16 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation47_127_167_implies_Equation315 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation315 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x]
  conv => enter [1]; rw [← l6 y x]

theorem Equation47_127_167_implies_Equation209 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h167 : Equation167 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
    conv => enter [1, 2, 1]; rw [← h167 X0 X0]
    conv => enter [1, 1]; rw [← h167 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l2 X0]
  have l5 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l6 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1]; rw [l8 y (y ◇ x)]
  conv => enter [1, 1]; rw [l9 y x]

theorem Equation167_209_implies_Equation3 (G : Type*) [Magma G] (h167 : Equation167 G) (h209 : Equation209 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h209 X0 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation117_167_implies_Equation3 (G : Type*) [Magma G] (h117 : Equation117 G) (h167 : Equation167 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h117 X0 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation167_205_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h205 : Equation205 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h205 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation104_167_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h167 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h104 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation166_255_implies_Equation28 (G : Type*) [Magma G] (h166 : Equation166 G) (h255 : Equation255 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h166 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h166 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 1]; rw [l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l0 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation47_152_implies_Equation9 (G : Type*) [Magma G] (h47 : Equation47 G) (h152 : Equation152 G) : Equation9 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h152 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h152 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2]; rw [l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation166_203_implies_Equation28 (G : Type*) [Magma G] (h166 : Equation166 G) (h203 : Equation203 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation99_152_implies_Equation9 (G : Type*) [Magma G] (h99 : Equation99 G) (h152 : Equation152 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h99 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation159_260_implies_Equation3 (G : Type*) [Magma G] (h159 : Equation159 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h260 X0 ((X0 ◇ X0) ◇ X0)]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation49_159_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h159 : Equation159 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ (X0 ◇ X0))]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation159_203_264_implies_Equation3 (G : Type*) [Magma G] (h159 : Equation159 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l1 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation75_99_159_implies_Equation3 (G : Type*) [Magma G] (h75 : Equation75 G) (h99 : Equation99 G) (h159 : Equation159 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h75 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l1 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation159_231_283_implies_Equation5 (G : Type*) [Magma G] (h159 : Equation159 G) (h231 : Equation231 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h231 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation56_108_159_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h108 : Equation108 G) (h159 : Equation159 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h108 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation159_212_255_implies_Equation258 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation258 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l6 (x ◇ x) y]

theorem Equation159_212_255_implies_Equation26 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation26 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation159_212_255_implies_Equation362 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation362 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x]
  conv => enter [1]; rw [← l6 x y]

theorem Equation159_212_255_implies_Equation209 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation209 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l6 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1, 1]; rw [l7 x y]

theorem Equation159_212_255_implies_Equation325 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation325 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l6 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation47_127_159_implies_Equation72 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation72 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation47_127_159_implies_Equation16 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation16 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation47_127_159_implies_Equation315 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation315 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x]
  conv => enter [1]; rw [← l6 y x]

theorem Equation47_127_159_implies_Equation117 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation117 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l6 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2]; rw [l7 y x]

theorem Equation47_127_159_implies_Equation385 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation385 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
    conv => enter [1, 2, 1]; rw [← h159 X0 X0]
    conv => enter [1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l6 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation159_212_221_implies_Equation2 (G : Type*) [Magma G] (h159 : Equation159 G) (h212 : Equation212 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [← h221 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 (X1 ◇ X2)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h212 X0 X1]
    conv => enter [1]; rw [l7 X1 (X0 ◇ (X1 ◇ X1))]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X1 ((X0 ◇ X0) ◇ (X1 ◇ X0))]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [← h221 X0 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0]
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 1]; rw [l10 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [l10 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l10 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation105_127_159_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h127 : Equation127 G) (h159 : Equation159 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h159 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h105 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 X1 X2]
  have l5 : ∀ X2 X1 X0 : G, (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  have l6 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (((X0 ◇ X1) ◇ X0) ◇ X1) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X1) ◇ X0) X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h127 X0 X1]
    conv => enter [1]; rw [l7 X1 ((X1 ◇ X1) ◇ X0)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X1 ((X0 ◇ X1) ◇ (X0 ◇ X0))]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l7 X0 X0]
    conv => enter [1]; rw [← h105 X0 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [l10 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 1]; rw [l10 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l10 X0]
  have l15 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l12 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l15 X1 X0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation159_209_255_implies_Equation3 (G : Type*) [Magma G] (h159 : Equation159 G) (h209 : Equation209 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l2 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X0]
  intro x
  conv => enter [1]; rw [← l6 x]

theorem Equation47_117_159_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h117 : Equation117 G) (h159 : Equation159 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h159 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [l0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l2 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2]; rw [← l4 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h159 X0 X0]
    conv => enter [1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X0]
  intro x
  conv => enter [1]; rw [← l6 x]

theorem Equation159_167_implies_Equation2 (G : Type*) [Magma G] (h159 : Equation159 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h167 X0 X1]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation156_255_implies_Equation257 (G : Type*) [Magma G] (h156 : Equation156 G) (h255 : Equation255 G) : Equation257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h156 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h156 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1, 1]; rw [← l1 x]

theorem Equation156_255_implies_Equation25 (G : Type*) [Magma G] (h156 : Equation156 G) (h255 : Equation255 G) : Equation25 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h156 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h156 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation156_255_implies_Equation361 (G : Type*) [Magma G] (h156 : Equation156 G) (h255 : Equation255 G) : Equation361 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h156 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h156 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x]
  conv => enter [1]; rw [← l2 x y]

theorem Equation47_153_implies_Equation52 (G : Type*) [Magma G] (h47 : Equation47 G) (h153 : Equation153 G) : Equation52 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h153 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h153 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2, 2]; rw [← l1 x]

theorem Equation47_153_implies_Equation10 (G : Type*) [Magma G] (h47 : Equation47 G) (h153 : Equation153 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h153 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h153 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation47_153_implies_Equation309 (G : Type*) [Magma G] (h47 : Equation47 G) (h153 : Equation153 G) : Equation309 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h153 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h153 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x]
  conv => enter [1]; rw [← l2 x y]

theorem Equation156_221_implies_Equation257 (G : Type*) [Magma G] (h156 : Equation156 G) (h221 : Equation221 G) : Equation257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h156 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 1, 1]; rw [← l0 x]

theorem Equation105_153_implies_Equation52 (G : Type*) [Magma G] (h105 : Equation105 G) (h153 : Equation153 G) : Equation52 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h153 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 2, 2]; rw [← l0 x]

theorem Equation156_212_implies_Equation24 (G : Type*) [Magma G] (h156 : Equation156 G) (h212 : Equation212 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h156 X0 X1]
    conv => enter [1]; rw [← h212 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 (X0 ◇ X1) X2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation127_153_implies_Equation13 (G : Type*) [Magma G] (h127 : Equation127 G) (h153 : Equation153 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h153 X0 X1]
    conv => enter [1]; rw [← h127 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation156_209_implies_Equation24 (G : Type*) [Magma G] (h156 : Equation156 G) (h209 : Equation209 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h156 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h156 X0 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation117_153_implies_Equation13 (G : Type*) [Magma G] (h117 : Equation117 G) (h153 : Equation153 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h153 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h153 X0 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation156_167_implies_Equation2 (G : Type*) [Magma G] (h156 : Equation156 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h156 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h156 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h156 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l2 X0 X2]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← h167 X2 X0]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 (X0 ◇ X1) X2 (X1 ◇ X0)]
    conv => enter [1]; rw [← h167 X1 X0]
  have l6 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l5 X1 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [l4 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation153_167_implies_Equation2 (G : Type*) [Magma G] (h153 : Equation153 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h153 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h153 X0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h153 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l2 X0 X2]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X2) ◇ (X1 ◇ X0)) = X2 := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [l3 X1 X0 X2]
    conv => enter [1]; rw [← h167 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = X1 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l3 X2 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h167 X1 X0]
  have l6 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l5 (X1 ◇ X2) X1 X1]
    conv => enter [1]; rw [l4 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation153_255_implies_Equation52 (G : Type*) [Magma G] (h153 : Equation153 G) (h255 : Equation255 G) : Equation52 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h153 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2, 2]; rw [← l1 x]

theorem Equation47_156_implies_Equation257 (G : Type*) [Magma G] (h47 : Equation47 G) (h156 : Equation156 G) : Equation257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h156 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1, 1]; rw [← l1 x]

theorem Equation153_203_implies_Equation23 (G : Type*) [Magma G] (h153 : Equation153 G) (h203 : Equation203 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h153 X0 (X0 ◇ (X0 ◇ X0))]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_156_implies_Equation8 (G : Type*) [Magma G] (h99 : Equation99 G) (h156 : Equation156 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h156 X0 ((X0 ◇ X0) ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation153_159_166_implies_Equation13 (G : Type*) [Magma G] (h153 : Equation153 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h153 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h166 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h166 X1 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation152_156_159_implies_Equation24 (G : Type*) [Magma G] (h152 : Equation152 G) (h156 : Equation156 G) (h159 : Equation159 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h156 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h152 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h152 X1 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation152_273_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h273 X0 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← l1 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1, 2]; rw [l4 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l4 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← h273 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation53_166_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h166 : Equation166 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h166 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h53 X0 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 (X0 ◇ X0) X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h166 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 1]; rw [l4 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l4 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [← h53 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation152_264_implies_Equation9 (G : Type*) [Magma G] (h152 : Equation152 G) (h264 : Equation264 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 1, 2]; rw [← h264 X0 X1]
    conv => enter [1, 2]; rw [← h264 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h264 X0 X0]
    conv => enter [1]; rw [← l2 X0 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h152 ((X0 ◇ X0) ◇ X0) ((X0 ◇ X0) ◇ X0)]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l4 X0]
    conv => enter [1]; rw [← h152 X0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h264 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l6 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

end Order3
