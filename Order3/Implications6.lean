import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation75_166_implies_Equation28 (G : Type*) [Magma G] (h75 : Equation75 G) (h166 : Equation166 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h166 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h75 X0 X1]
    conv => enter [1, 1]; rw [← h75 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h75 X0 X0]
    conv => enter [1]; rw [← l2 X0 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h166 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l4 X0]
    conv => enter [1]; rw [← h166 X0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l6 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l6 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation152_231_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h231 : Equation231 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h152 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [← h231 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h231 (X1 ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h231 X1 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation108_166_implies_Equation2 (G : Type*) [Magma G] (h108 : Equation108 G) (h166 : Equation166 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h108 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h108 ((X1 ◇ X1) ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h108 X1 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation152_221_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h152 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h221 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [← h221 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation105_166_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h166 : Equation166 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h166 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h105 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h105 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation152_212_255_implies_Equation258 (G : Type*) [Magma G] (h152 : Equation152 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation258 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h152 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h152 X0 X0]
    conv => enter [1, 1, 2]; rw [← h152 X0 X0]
    conv => enter [1, 2]; rw [← h152 X0 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h152 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l4 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1, 1, 2]; rw [← l1 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 1]; rw [l6 X0 (X0 ◇ X0)]
  have l9 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [← l8 X0]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l9 X0]
    conv => enter [1]; rw [← h152 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 1]; rw [l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 x]
  conv => enter [1]; rw [← l13 (x ◇ x) y]

theorem Equation47_127_166_implies_Equation72 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h166 : Equation166 G) : Equation72 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h166 X0 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h166 X0 X0]
    conv => enter [1, 2, 1]; rw [← h166 X0 X0]
    conv => enter [1, 1]; rw [← h166 X0 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h166 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1, 2, 1]; rw [← l1 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [l6 (X0 ◇ X0) X0]
  have l9 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [← l8 X0]
  have l10 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l9 X0]
    conv => enter [1]; rw [← h166 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2]; rw [l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [l10 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x]
  conv => enter [1]; rw [← l13 y (x ◇ x)]

theorem Equation152_209_255_implies_Equation9 (G : Type*) [Magma G] (h152 : Equation152 G) (h209 : Equation209 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h152 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
    conv => enter [1, 2, 2]; rw [← h152 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h255 X0]
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ X0) ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1, 2, 2]; rw [← l4 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X0)]
  have l8 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2, 1]; rw [l2 X0]
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l8 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [l1 X0 (X0 ◇ X0)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l10 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l10 X0]
  intro x y
  conv => enter [1]; rw [← l11 x y]

theorem Equation47_117_166_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h117 : Equation117 G) (h166 : Equation166 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h166 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
    conv => enter [1, 1, 1]; rw [← h166 X0 X1]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h47 X0]
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1, 1, 1]; rw [← l4 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X0]
  have l8 : ∀ X0 : G, ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 2]; rw [l2 X0]
    conv => enter [1]; rw [← l3 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l8 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0) X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l10 X0]
  intro x y
  conv => enter [1]; rw [← l11 y x]

theorem Equation152_205_255_implies_Equation9 (G : Type*) [Magma G] (h152 : Equation152 G) (h205 : Equation205 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h255 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 1]; rw [← h255 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l1 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h255 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation47_104_166_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h166 : Equation166 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h47 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l1 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h47 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation152_167_255_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h167 : Equation167 G) (h255 : Equation255 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h152 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 1]; rw [l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l6 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [l8 X0]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l8 X0]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l8 (X1 ◇ X0)]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [← h167 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation47_166_167_implies_Equation2 (G : Type*) [Magma G] (h47 : Equation47 G) (h166 : Equation166 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X0]
  have l5 : ∀ X0 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2]; rw [l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l6 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l8 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l8 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l9 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation152_167_203_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h167 : Equation167 G) (h203 : Equation203 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h152 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h152 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h152 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← h152 X0 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h152 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2, 2]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1, 2]; rw [l5 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l5 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l8 X0]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 2]; rw [l8 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l8 (X1 ◇ X0)]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l10 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [← h167 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation99_166_167_implies_Equation2 (G : Type*) [Magma G] (h99 : Equation99 G) (h166 : Equation166 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h166 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 1, 1, 1]; rw [← h166 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h166 X0 (((X0 ◇ X0) ◇ X0) ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 1, 1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1, 1]; rw [l5 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l5 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1, 1]; rw [l8 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l8 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l10 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation152_159_255_implies_Equation9 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h255 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation152_159_255_implies_Equation377 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h255 : Equation255 G) : Equation377 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h255 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation152_159_255_implies_Equation101 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h255 : Equation255 G) : Equation101 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h255 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1, 1]; rw [← l3 X0]
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation47_159_166_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation47_159_166_implies_Equation333 (G : Type*) [Magma G] (h47 : Equation47 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h166 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation47_159_166_implies_Equation208 (G : Type*) [Magma G] (h47 : Equation47 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation208 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h159 X0 (X1 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2, 2]; rw [← l3 X0]
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation152_159_166_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h159 : Equation159 G) (h166 : Equation166 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h166 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, ((X2 ◇ X2) ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← h152 X2 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 (X1 ◇ X2) (X2 ◇ X1)]
    conv => enter [1]; rw [← h159 X2 X1]
  have l6 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l5 (X2 ◇ X2) X1 X1]
    conv => enter [1]; rw [l4 X2 X1 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation152_156_166_implies_Equation153 (G : Type*) [Magma G] (h152 : Equation152 G) (h156 : Equation156 G) (h166 : Equation166 G) : Equation153 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h156 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h166 X0 X1]
    conv => enter [1, 1, 1]; rw [h166 X0 X1]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation152_153_166_implies_Equation156 (G : Type*) [Magma G] (h152 : Equation152 G) (h153 : Equation153 G) (h166 : Equation166 G) : Equation156 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h166 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h153 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h152 X0 X1]
    conv => enter [1, 2, 2]; rw [h152 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation99_255_308_implies_Equation9 (G : Type*) [Magma G] (h99 : Equation99 G) (h255 : Equation255 G) (h308 : Equation308 G) : Equation9 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h308 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l1 X0]
    conv => enter [1, 2, 1]; rw [l1 X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h99 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 1]; rw [l1 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← h99 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← l2 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h255 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h308 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation47_203_364_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h203 : Equation203 G) (h364 : Equation364 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [← l0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1, 1, 2]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h203 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l1 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← h203 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← l2 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h47 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h364 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation99_273_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h273 : Equation273 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation53_203_implies_Equation3 (G : Type*) [Magma G] (h53 : Equation53 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_264_307_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h264 : Equation264 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h264 X0 X0]
    conv => enter [1, 1, 1]; rw [← l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h264 X0 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation75_203_359_implies_Equation3 (G : Type*) [Magma G] (h75 : Equation75 G) (h203 : Equation203 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h203 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h75 X0 X0]
    conv => enter [1, 2, 2]; rw [← l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation99_264_283_implies_Equation108 (G : Type*) [Magma G] (h99 : Equation99 G) (h264 : Equation264 G) (h283 : Equation283 G) : Equation108 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h283 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X1) ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [h99 x]
  conv => enter [1, 2]; rw [l0 x y]

theorem Equation56_75_203_implies_Equation231 (G : Type*) [Magma G] (h56 : Equation56 G) (h75 : Equation75 G) (h203 : Equation203 G) : Equation231 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h56 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X1 ◇ X1)) X0]
  intro x y
  conv => enter [1]; rw [h203 x]
  conv => enter [1, 1]; rw [l0 x y]

theorem Equation99_263_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h263 : Equation263 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h263 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation55_203_implies_Equation3 (G : Type*) [Magma G] (h55 : Equation55 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h55 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_261_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h261 : Equation261 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h261 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2]; rw [← l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h99 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l5 X0]
  intro x
  conv => enter [1]; rw [← l7 x]

theorem Equation65_203_implies_Equation3 (G : Type*) [Magma G] (h65 : Equation65 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h65 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← l1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h203 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l5 X0]
  intro x
  conv => enter [1]; rw [← l7 x]

theorem Equation99_260_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h260 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation49_203_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_257_implies_Equation25 (G : Type*) [Magma G] (h99 : Equation99 G) (h257 : Equation257 G) : Equation25 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1]; rw [← h257 X0 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation99_257_implies_Equation156 (G : Type*) [Magma G] (h99 : Equation99 G) (h257 : Equation257 G) : Equation156 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1]; rw [← h257 X0 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2]; rw [← l1 x]

theorem Equation52_203_implies_Equation10 (G : Type*) [Magma G] (h52 : Equation52 G) (h203 : Equation203 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 (X0 ◇ X0)]
    conv => enter [1]; rw [← h52 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation52_203_implies_Equation153 (G : Type*) [Magma G] (h52 : Equation52 G) (h203 : Equation203 G) : Equation153 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 (X0 ◇ X0)]
    conv => enter [1]; rw [← h52 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [← l1 x]

theorem Equation99_203_264_implies_Equation47 (G : Type*) [Magma G] (h99 : Equation99 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation47 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h264 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation75_99_203_implies_Equation255 (G : Type*) [Magma G] (h75 : Equation75 G) (h99 : Equation99 G) (h203 : Equation203 G) : Equation255 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h75 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_221_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h221 : Equation221 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h221 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation105_203_implies_Equation3 (G : Type*) [Magma G] (h105 : Equation105 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h105 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation99_219_implies_Equation14 (G : Type*) [Magma G] (h99 : Equation99 G) (h219 : Equation219 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h99 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation115_203_implies_Equation14 (G : Type*) [Magma G] (h115 : Equation115 G) (h203 : Equation203 G) : Equation14 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h203 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h115 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h115 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation99_211_231_implies_Equation5 (G : Type*) [Magma G] (h99 : Equation99 G) (h211 : Equation211 G) (h231 : Equation231 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h211 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h99 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation107_108_203_implies_Equation4 (G : Type*) [Magma G] (h107 : Equation107 G) (h108 : Equation108 G) (h203 : Equation203 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h203 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h107 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation99_209_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h209 : Equation209 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h209 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation117_203_implies_Equation3 (G : Type*) [Magma G] (h117 : Equation117 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h117 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_205_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h205 : Equation205 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h205 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation104_203_implies_Equation3 (G : Type*) [Magma G] (h104 : Equation104 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h104 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_151_212_255_implies_Equation47 (G : Type*) [Magma G] (h99 : Equation99 G) (h151 : Equation151 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation47 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h151 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation47_127_151_203_implies_Equation255 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h151 : Equation151 G) (h203 : Equation203 G) : Equation255 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h127 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h151 X0]
  have l2 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation99_167_255_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h167 : Equation167 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation47_167_203_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h167 : Equation167 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_159_255_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h159 : Equation159 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h159 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation47_159_203_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h159 : Equation159 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h159 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_159_212_implies_Equation258 (G : Type*) [Magma G] (h99 : Equation99 G) (h159 : Equation159 G) (h212 : Equation212 G) : Equation258 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 : G, (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h212 X0 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2]; rw [l5 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 1]; rw [← l5 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l12 (x ◇ x) y]

theorem Equation127_159_203_implies_Equation72 (G : Type*) [Magma G] (h127 : Equation127 G) (h159 : Equation159 G) (h203 : Equation203 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h159 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 : G, (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l2 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h127 X0 X0]
  have l6 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l1 (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 (((X0 ◇ X0) ◇ X1) ◇ X0)]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 1, 1]; rw [l5 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x]
  conv => enter [1]; rw [← l12 y (x ◇ x)]

theorem Equation117_255_implies_Equation3 (G : Type*) [Magma G] (h117 : Equation117 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1, 1, 1]; rw [h255 X0]
    conv => enter [1]; rw [l0 ((X0 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h117 X0 X0]
    conv => enter [1]; rw [l1 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation47_209_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h209 : Equation209 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1, 2, 2]; rw [h47 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h209 X0 X0]
    conv => enter [1]; rw [l1 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation115_255_implies_Equation14 (G : Type*) [Magma G] (h115 : Equation115 G) (h255 : Equation255 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h115 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h115 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation47_219_implies_Equation14 (G : Type*) [Magma G] (h47 : Equation47 G) (h219 : Equation219 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation108_280_implies_Equation2 (G : Type*) [Magma G] (h108 : Equation108 G) (h280 : Equation280 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h280 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1]; rw [← h108 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h108 (X1 ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 1]; rw [l4 X0 X2]
    conv => enter [1]; rw [← h108 X1 X2]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h280 X1 X1]
  have l7 : ∀ X1 X2 : G, (X1 ◇ X2) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l6 X1 X2]
    conv => enter [1]; rw [l5 X1 X1 X2]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l6 X0 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation50_231_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h231 : Equation231 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h50 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2]; rw [← h231 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h231 (X1 ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X1)]
  have l5 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 1, 2]; rw [l4 X0 X2]
    conv => enter [1]; rw [← h231 X1 X2]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h50 X1 X1]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1, 1]; rw [← l6 X2 X2]
    conv => enter [1]; rw [l5 X2 X2 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l6 X0 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation108_231_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation108_231_implies_Equation283 (G : Type*) [Magma G] (h108 : Equation108 G) (h231 : Equation231 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h231 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation108_211_implies_Equation4 (G : Type*) [Magma G] (h108 : Equation108 G) (h211 : Equation211 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h211 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h211 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation107_231_implies_Equation5 (G : Type*) [Magma G] (h107 : Equation107 G) (h231 : Equation231 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h107 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h107 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation107_283_implies_Equation5 (G : Type*) [Magma G] (h107 : Equation107 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h107 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1, 2]; rw [h283 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation56_211_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h211 : Equation211 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h211 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1, 1]; rw [h56 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation107_108_255_implies_Equation4 (G : Type*) [Magma G] (h107 : Equation107 G) (h108 : Equation108 G) (h255 : Equation255 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h107 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h108 (X0 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h107 X1 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l0 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h108 ((X0 ◇ X0) ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l2 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1]; rw [← h108 ((X0 ◇ X0) ◇ X0) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1, 1]; rw [l2 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation47_211_231_implies_Equation5 (G : Type*) [Magma G] (h47 : Equation47 G) (h211 : Equation211 G) (h231 : Equation231 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h211 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1]; rw [← h231 (X0 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h211 X1 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h231 (X0 ◇ (X0 ◇ X0)) X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l2 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h231 (X0 ◇ (X0 ◇ X0)) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [l2 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation105_255_implies_Equation3 (G : Type*) [Magma G] (h105 : Equation105 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h105 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h105 X0 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation47_221_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h221 : Equation221 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h221 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h221 X0 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation104_255_implies_Equation3 (G : Type*) [Magma G] (h104 : Equation104 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h104 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation47_205_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h205 : Equation205 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h205 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation47_273_280_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h273 : Equation273 G) (h280 : Equation280 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 X0 (X1 ◇ X1)]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l3 X0]
    conv => enter [1]; rw [← h280 X1 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 X1 X2 : G, ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l7 X1]
    conv => enter [1]; rw [← h280 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation47_273_280_implies_Equation333 (G : Type*) [Magma G] (h47 : Equation47 G) (h273 : Equation273 G) (h280 : Equation280 G) : Equation333 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 X0 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l5 X0]
    conv => enter [1]; rw [← h280 X1 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 X1 X2 : G, ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l9 X1]
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation47_273_280_implies_Equation208 (G : Type*) [Magma G] (h47 : Equation47 G) (h273 : Equation273 G) (h280 : Equation280 G) : Equation208 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h47 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 X0 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l5 X0]
    conv => enter [1]; rw [← h280 X1 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 X1 X2 : G, ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l9 X1]
    conv => enter [1]; rw [← h280 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l9 X1]
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]
  conv => enter [1, 1]; rw [l11 y x]

theorem Equation50_53_255_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h53 : Equation53 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h255 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l3 X0]
    conv => enter [1]; rw [← h50 X1 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h50 X2 (X0 ◇ ((X1 ◇ X1) ◇ X0))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l7 X1]
    conv => enter [1]; rw [← h50 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation50_53_255_implies_Equation377 (G : Type*) [Magma G] (h50 : Equation50 G) (h53 : Equation53 G) (h255 : Equation255 G) : Equation377 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h255 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l3 X0 (X1 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l5 X0]
    conv => enter [1]; rw [← h50 X1 ((X0 ◇ X0) ◇ X0)]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h50 X2 (X0 ◇ ((X1 ◇ X1) ◇ X0))]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X1]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 2]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation50_53_255_implies_Equation101 (G : Type*) [Magma G] (h50 : Equation50 G) (h53 : Equation53 G) (h255 : Equation255 G) : Equation101 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h53 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h255 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l3 X0 (X1 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l5 X0]
    conv => enter [1]; rw [← h50 X1 ((X0 ◇ X0) ◇ X0)]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h50 X2 (X0 ◇ ((X1 ◇ X1) ◇ X0))]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l9 X1]
    conv => enter [1]; rw [← h50 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X1]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 2]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [← l10 x y]
  conv => enter [1, 2]; rw [l11 x y]

theorem Equation47_264_273_implies_Equation151 (G : Type*) [Magma G] (h47 : Equation47 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h273 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 1]; rw [← h47 sK0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h273 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h264 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h264 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0]
  intro x
  conv => enter [1]; rw [l5 x]

theorem Equation53_75_255_implies_Equation151 (G : Type*) [Magma G] (h53 : Equation53 G) (h75 : Equation75 G) (h255 : Equation255 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h255 sK0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53 ((sK0 ◇ sK0) ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h75 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h75 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0]
  intro x
  conv => enter [1]; rw [l5 x]

theorem Equation47_261_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h261 : Equation261 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1, 2, 1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 1]; rw [l1 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h47 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation65_255_implies_Equation3 (G : Type*) [Magma G] (h65 : Equation65 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h65 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 1, 2]; rw [l1 X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2]; rw [l1 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h255 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l5 x]

theorem Equation47_260_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h260 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation49_255_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h49 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation47_203_264_implies_Equation99 (G : Type*) [Magma G] (h47 : Equation47 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation99 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [h47 x]
  conv => enter [1, 2]; rw [l0 x]

theorem Equation75_99_255_implies_Equation203 (G : Type*) [Magma G] (h75 : Equation75 G) (h99 : Equation99 G) (h255 : Equation255 G) : Equation203 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h75 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [h255 x]
  conv => enter [1, 1]; rw [l0 x]

theorem Equation47_151_212_255_implies_Equation99 (G : Type*) [Magma G] (h47 : Equation47 G) (h151 : Equation151 G) (h212 : Equation212 G) (h255 : Equation255 G) : Equation99 G := by
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
  intro x
  conv => enter [1]; rw [h47 x]
  conv => enter [1, 2]; rw [l1 x]

theorem Equation47_127_151_255_implies_Equation203 (G : Type*) [Magma G] (h47 : Equation47 G) (h127 : Equation127 G) (h151 : Equation151 G) (h255 : Equation255 G) : Equation203 G := by
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
  intro x
  conv => enter [1]; rw [h255 x]
  conv => enter [1, 1]; rw [l1 x]

theorem Equation159_264_273_implies_Equation75 (G : Type*) [Magma G] (h159 : Equation159 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation75 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h273 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h159 sK1 sK0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h264 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 1, 1]; rw [← h273 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h264 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 1, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h264 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation53_75_159_implies_Equation264 (G : Type*) [Magma G] (h53 : Equation53 G) (h75 : Equation75 G) (h159 : Equation159 G) : Equation264 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h159 sK1 sK0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h75 (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h53 ((sK0 ◇ sK1) ◇ sK1) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h159 (sK1 ◇ sK0) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK1) ◇ sK1) (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation99_211_264_implies_Equation50 (G : Type*) [Magma G] (h99 : Equation99 G) (h211 : Equation211 G) (h264 : Equation264 G) : Equation50 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h211 X0 X1]
    conv => enter [1]; rw [← h264 (X0 ◇ (X1 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h99 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation75_107_203_implies_Equation280 (G : Type*) [Magma G] (h75 : Equation75 G) (h107 : Equation107 G) (h203 : Equation203 G) : Equation280 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h107 X0 X1]
    conv => enter [1]; rw [← h75 ((X1 ◇ X1) ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h203 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation99_212_231_implies_Equation56 (G : Type*) [Magma G] (h99 : Equation99 G) (h212 : Equation212 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h231 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ (X1 ◇ X1)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h99 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation108_127_203_implies_Equation283 (G : Type*) [Magma G] (h108 : Equation108 G) (h127 : Equation127 G) (h203 : Equation203 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h108 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 ((X1 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h203 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation127_151_212_264_implies_Equation56 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h212 : Equation212 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h212 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [← h127 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l7 X1 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X0]
  have l10 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) = (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h127 ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) X1]
    conv => enter [1, 2]; rw [l3 (X1 ◇ X1) X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X1 X1]
    conv => enter [1, 1, 1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2, 2, 1]; rw [l1 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X0 ◇ X1))]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [l11 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 X0 X1]
    conv => enter [1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [l11 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h212 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l11 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← l13 X0 X1]
  have l18 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l19 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 1, 2, 2]; rw [← l15 X0 X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 1]; rw [← h212 X0 X1]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1, 2, 2]; rw [← l12 X0 X1]
  have l28 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) X1]
    conv => enter [1, 1, 2, 2]; rw [← l12 X0 X1]
  have l29 : ∀ X1 X0 : G, ((X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l28 X1 X0]
    conv => enter [1]; rw [l11 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l27 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l24 X1 X0]
    conv => enter [1]; rw [l26 X1 X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l24 X0 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l25 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l30 X1 X0]
    conv => enter [1]; rw [l29 X1 X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l11 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l32 X0 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1, 2, 2]; rw [← l31 X1 X0]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l31 X1 X0]
    conv => enter [1]; rw [l34 X0 X1]
  have l37 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l35 X0 X1]
    conv => enter [1]; rw [l36 X0 X1]
  have l38 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l37 X1 X0]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X1 ◇ X0))]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [l38 X1 X0]
  have l40 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l39 X0 X0]
    conv => enter [1]; rw [l18 X1 X0 (X0 ◇ X0)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l40 X1 X0]
  have l42 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l41 X1 X0]
  have l43 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l39 X0 X0]
    conv => enter [1]; rw [l42 X1 X0]
  intro x y
  conv => enter [1]; rw [← l43 x y]

theorem Equation127_151_212_264_implies_Equation75 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h212 : Equation212 G) (h264 : Equation264 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h212 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [← h127 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l7 X1 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X0]
  have l10 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) = (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h127 ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) X1]
    conv => enter [1, 2]; rw [l3 (X1 ◇ X1) X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X1 X1]
    conv => enter [1, 1, 1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2, 2, 1]; rw [l1 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X0 ◇ X1))]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [l11 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 X0 X1]
    conv => enter [1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [l11 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h212 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← l13 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l17 X1 X0]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 1, 2, 2]; rw [← l15 X0 X1]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 1]; rw [← h212 X0 X1]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l21 X1 X0]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 X1 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1, 2, 2]; rw [← l12 X0 X1]
  have l26 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l18 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) X1]
    conv => enter [1, 1, 2, 2]; rw [← l12 X0 X1]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l26 X1 X0]
    conv => enter [1]; rw [l11 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l28 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l25 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l22 X1 X0]
    conv => enter [1]; rw [l24 X1 X0]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l22 X0 ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l23 X0 X1]
  have l31 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l28 X1 X0]
    conv => enter [1]; rw [l27 X1 X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l11 (X1 ◇ (X1 ◇ X0)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l30 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1, 2, 2]; rw [← l29 X1 X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l29 X1 X0]
    conv => enter [1]; rw [l32 X0 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l33 X0 X1]
    conv => enter [1]; rw [l34 X0 X1]
  intro x y
  conv => enter [1]; rw [← l35 y x]

theorem Equation75_127_151_212_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h127 : Equation127 G) (h151 : Equation151 G) (h212 : Equation212 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h127 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h212 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l8 X0 (X1 ◇ X0)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h212 ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) X1]
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X1]
    conv => enter [1, 2, 2]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 1, 1, 2]; rw [l1 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l11 ((X1 ◇ X0) ◇ X0) X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (((X1 ◇ X0) ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1, 1]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h127 X0 X1]
    conv => enter [1, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [l11 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h127 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l11 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 (((X1 ◇ X0) ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← l13 X0 X1]
  have l18 : ∀ X1 X0 X2 : G, ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X2]
  have l19 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 1]; rw [l19 X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 (X0 ◇ X1) ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1, 1]; rw [← l15 X0 X1]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 2]; rw [← h127 X0 X1]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ X0 X1 : G, ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l1 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l26 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l2 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l27 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← l12 X0 X1]
  have l28 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (X1 ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 2, 1, 1]; rw [← l12 X0 X1]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1)) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l28 X0 X1]
    conv => enter [1]; rw [l11 (((X0 ◇ X1) ◇ X1) ◇ X1) ((X0 ◇ X1) ◇ X1)]
  have l30 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l27 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l31 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l24 X0 X1]
    conv => enter [1]; rw [l26 X0 X1]
  have l32 : ∀ X0 X1 : G, (((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l24 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1]; rw [l25 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l30 X0 X1]
    conv => enter [1]; rw [l29 X1 X0]
  have l34 : ∀ X0 X1 : G, ((((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l32 X0 X1]
  have l35 : ∀ X1 X0 : G, (X1 ◇ X0) = (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1, 1, 1]; rw [← l31 X0 X1]
  have l36 : ∀ X0 X1 : G, (((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1, 1, 1]; rw [l31 X0 X1]
    conv => enter [1]; rw [l34 X0 X1]
  have l37 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l35 X1 X0]
    conv => enter [1]; rw [l36 X0 X1]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l37 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X1) X1]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 1]; rw [l38 X0 X1]
  have l40 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l39 X0 X0]
    conv => enter [1]; rw [l18 (X0 ◇ X0) X0 X1]
  have l41 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l40 X0 X1]
  have l42 : ∀ X0 X1 : G, (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l41 X0 X1]
  have l43 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l39 X0 X0]
    conv => enter [1]; rw [l42 X0 X1]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l43 X1 X0]
    conv => enter [1]; rw [l37 ((X1 ◇ X1) ◇ X1) X0]
  have l45 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l44 X0 X1]
    conv => enter [1]; rw [← h127 X1 X1]
  intro x y
  conv => enter [1]; rw [← l45 x x]
  conv => enter [1, 2]; rw [l44 x y]
  conv => enter [1, 2]; rw [l0 y y]

theorem Equation75_127_151_212_implies_Equation264 (G : Type*) [Magma G] (h75 : Equation75 G) (h127 : Equation127 G) (h151 : Equation151 G) (h212 : Equation212 G) : Equation264 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h127 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h212 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l8 X0 (X1 ◇ X0)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h212 ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) X1]
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X1]
    conv => enter [1, 2, 2]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 1, 1, 2]; rw [l1 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l11 ((X1 ◇ X0) ◇ X0) X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (((X1 ◇ X0) ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1, 1]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h127 X0 X1]
    conv => enter [1, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [l11 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h127 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 (((X1 ◇ X0) ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← l13 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 (X0 ◇ X1) ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1, 1]; rw [← l15 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← h127 X0 X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l21 X0 X1]
  have l23 : ∀ X0 X1 : G, ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l1 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l2 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← l12 X0 X1]
  have l26 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (X1 ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X1]
    conv => enter [1, 2, 1, 1]; rw [← l12 X0 X1]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1)) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l26 X0 X1]
    conv => enter [1]; rw [l11 (((X0 ◇ X1) ◇ X1) ◇ X1) ((X0 ◇ X1) ◇ X1)]
  have l28 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l25 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  have l29 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l22 X0 X1]
    conv => enter [1]; rw [l24 X0 X1]
  have l30 : ∀ X0 X1 : G, (((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l22 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1]; rw [l23 X0 X1]
  have l31 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l28 X0 X1]
    conv => enter [1]; rw [l27 X1 X0]
  have l32 : ∀ X0 X1 : G, ((((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l30 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ X0) = (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 1, 1]; rw [← l29 X0 X1]
  have l34 : ∀ X0 X1 : G, (((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1, 1, 1]; rw [l29 X0 X1]
    conv => enter [1]; rw [l32 X0 X1]
  have l35 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l33 X1 X0]
    conv => enter [1]; rw [l34 X0 X1]
  intro x y
  conv => enter [1]; rw [← l35 x y]

theorem Equation118_264_implies_Equation73 (G : Type*) [Magma G] (h118 : Equation118 G) (h264 : Equation264 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X1 X0]
    conv => enter [1]; rw [← h118 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation118_264_implies_Equation125 (G : Type*) [Magma G] (h118 : Equation118 G) (h264 : Equation264 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X1 X0]
    conv => enter [1]; rw [← h118 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h118 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [l0 y (y ◇ x)]

theorem Equation118_264_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h264 : Equation264 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X1 X0]
    conv => enter [1]; rw [← h118 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [l0 y (y ◇ (x ◇ y))]

theorem Equation75_229_implies_Equation73 (G : Type*) [Magma G] (h75 : Equation75 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h75 X1 X0]
    conv => enter [1]; rw [← h229 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h229 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l0 ((x ◇ y) ◇ y) y]
  conv => enter [1, 2]; rw [l0 (x ◇ y) y]

theorem Equation118_229_implies_Equation73 (G : Type*) [Magma G] (h118 : Equation118 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation118_229_implies_Equation125 (G : Type*) [Magma G] (h118 : Equation118 G) (h229 : Equation229 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1]; rw [l0 y (y ◇ x)]

theorem Equation118_229_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h229 : Equation229 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [h229 x y]
  conv => enter [1, 1]; rw [l0 y x]

theorem Equation118_229_implies_Equation43 (G : Type*) [Magma G] (h118 : Equation118 G) (h229 : Equation229 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation118_229_implies_Equation75 (G : Type*) [Magma G] (h118 : Equation118 G) (h229 : Equation229 G) : Equation75 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation118_151_212_222_274_implies_Equation66 (G : Type*) [Magma G] (h118 : Equation118 G) (h151 : Equation151 G) (h212 : Equation212 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h222 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h222 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h212 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h212 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h212 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l13 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X0) (X1 ◇ ((X0 ◇ X1) ◇ X0))]
  have l17 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l16 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0) X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 2, 2]; rw [l14 X1 X0]
    conv => enter [1, 2, 2]; rw [l14 X1 X0]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1, 1, 2]; rw [← l22 X1 X0]
    conv => enter [1, 2]; rw [← l22 X1 X0]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1]; rw [← l8 ((X0 ◇ X0) ◇ X1) X1]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [l20 (X0 ◇ X0) X1]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l26 X1 X0]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l10 (X1 ◇ (X1 ◇ (X0 ◇ X0))) (X1 ◇ (X0 ◇ X0))]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [← l27 (X1 ◇ (X0 ◇ X0)) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2]; rw [← l7 X1 (X1 ◇ (X0 ◇ X0))]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2, 2]; rw [l20 X1 (X0 ◇ X0)]
  have l32 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l21 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l31 X0 X1]
  have l33 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1]; rw [l32 X1 X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l34 y x]

theorem Equation118_151_212_222_274_implies_Equation73 (G : Type*) [Magma G] (h118 : Equation118 G) (h151 : Equation151 G) (h212 : Equation212 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h222 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h222 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h212 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h212 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h212 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l15 X1 X0]
    conv => enter [1]; rw [← l7 X1 ((X1 ◇ X1) ◇ X0)]
  have l18 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0) X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 2, 2]; rw [l15 X1 X0]
    conv => enter [1, 2, 2]; rw [l15 X1 X0]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 1, 2]; rw [← l21 X1 X0]
    conv => enter [1, 2]; rw [← l21 X1 X0]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [← l8 ((X0 ◇ X0) ◇ X1) X1]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1]; rw [l20 (X0 ◇ X0) X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l25 X1 X0]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← l26 X0 X1]
  have l28 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l5 ((X1 ◇ X1) ◇ X0) X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l4 (X1 ◇ (X0 ◇ X0)) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l30 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l29 X0 X1]
  have l31 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l27 ((X1 ◇ X1) ◇ X0) (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l28 X1 X0]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l31 X0 X1]
  have l33 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l26 X1 (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))]
    conv => enter [1]; rw [l32 X0 X1]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l17 X1 X0]
    conv => enter [1]; rw [l33 X0 X1]
  have l35 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l27 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l34 X0 X1]
  have l36 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l30 X0 X1]
    conv => enter [1]; rw [l35 X0 X1]
  have l37 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) X0]
    conv => enter [1]; rw [l36 X0 X1]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 ((X1 ◇ X1) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l37 X0 X1]
  have l39 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l26 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l38 X0 X1]
  have l40 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l26 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l39 X0 X1]
  have l41 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l40 X0 X1]
  intro x y
  conv => enter [1]; rw [← l41 y x]

theorem Equation118_151_212_222_274_implies_Equation125 (G : Type*) [Magma G] (h118 : Equation118 G) (h151 : Equation151 G) (h212 : Equation212 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h222 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h222 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h212 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h212 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h212 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l15 X1 X0]
    conv => enter [1]; rw [← l7 X1 ((X1 ◇ X1) ◇ X0)]
  have l18 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0) X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 2, 2]; rw [l15 X1 X0]
    conv => enter [1, 2, 2]; rw [l15 X1 X0]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 1, 2]; rw [← l21 X1 X0]
    conv => enter [1, 2]; rw [← l21 X1 X0]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [← l8 ((X0 ◇ X0) ◇ X1) X1]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1]; rw [l20 (X0 ◇ X0) X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l25 X1 X0]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← l26 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1]
  have l29 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l5 ((X1 ◇ X1) ◇ X0) X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l4 (X1 ◇ (X0 ◇ X0)) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l31 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l30 X0 X1]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l27 ((X1 ◇ X1) ◇ X0) (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l29 X1 X0]
  have l33 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l32 X0 X1]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l26 X1 (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))]
    conv => enter [1]; rw [l33 X0 X1]
  have l35 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l17 X1 X0]
    conv => enter [1]; rw [l34 X0 X1]
  have l36 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l27 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l35 X0 X1]
  have l37 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l31 X0 X1]
    conv => enter [1]; rw [l36 X0 X1]
  have l38 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) X0]
    conv => enter [1]; rw [l37 X0 X1]
  have l39 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 ((X1 ◇ X1) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l38 X0 X1]
  have l40 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l26 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l39 X0 X1]
  have l41 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l26 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l40 X0 X1]
  have l42 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l41 X0 X1]
  have l43 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l42 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h222 X0 X1]
  intro x y
  conv => enter [1]; rw [← l28 y x]
  conv => enter [1]; rw [← l43 y (y ◇ x)]

theorem Equation118_212_274_implies_Equation127 (G : Type*) [Magma G] (h118 : Equation118 G) (h212 : Equation212 G) (h274 : Equation274 G) : Equation127 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h212 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h212 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

end Order3
