import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation3_43_228_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h228 : Equation228 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h228 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_43_102_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h102 : Equation102 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h102 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [h43 (x ◇ y) y]

theorem Equation221_387_implies_Equation14 (G : Type*) [Magma G] (h221 : Equation221 G) (h387 : Equation387 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h387 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation43_105_332_implies_Equation14 (G : Type*) [Magma G] (h43 : Equation43 G) (h105 : Equation105 G) (h332 : Equation332 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h332 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1]; rw [h43 (x ◇ y) y]

theorem Equation43_209_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h209 : Equation209 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h209 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_117_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h117 : Equation117 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1]; rw [h43 (x ◇ y) x]
  conv => enter [1]; rw [h43 (x ◇ (x ◇ y)) y]

theorem Equation43_208_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h208 : Equation208 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_101_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h101 : Equation101 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_206_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h206 : Equation206 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation43_124_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h124 : Equation124 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1, 1]; rw [h43 y x]
  conv => enter [1, 1]; rw [h43 (x ◇ y) x]
  conv => enter [1]; rw [h43 (x ◇ (x ◇ y)) y]

theorem Equation43_205_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h205 : Equation205 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h205 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation43_104_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h104 : Equation104 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation3_395_implies_Equation238 (G : Type*) [Magma G] (h3 : Equation3 G) (h395 : Equation395 G) : Equation238 G := by
  intro x y z
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h395 x x z]
  conv => enter [1]; rw [h395 (z ◇ x) x y]

theorem Equation3_395_implies_Equation333 (G : Type*) [Magma G] (h3 : Equation3 G) (h395 : Equation395 G) : Equation333 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [← h395 X0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_327_implies_Equation103 (G : Type*) [Magma G] (h3 : Equation3 G) (h327 : Equation327 G) : Equation103 G := by
  intro x y z
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h327 x x y]
  conv => enter [1]; rw [h327 x (x ◇ y) z]

theorem Equation3_327_implies_Equation377 (G : Type*) [Magma G] (h3 : Equation3 G) (h327 : Equation327 G) : Equation377 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h327 (X0 ◇ X1) X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_26_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h26 : Equation26 G) : Equation258 G := by
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h26 (x ◇ x) y]

theorem Equation3_16_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h16 : Equation16 G) : Equation72 G := by
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h16 (x ◇ x) y]

theorem Equation26_104_implies_Equation4 (G : Type*) [Magma G] (h26 : Equation26 G) (h104 : Equation104 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h26 X1 X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation16_205_implies_Equation5 (G : Type*) [Magma G] (h16 : Equation16 G) (h205 : Equation205 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h16 X1 X0]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation26_55_implies_Equation105 (G : Type*) [Magma G] (h26 : Equation26 G) (h55 : Equation55 G) : Equation105 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation16_263_implies_Equation221 (G : Type*) [Magma G] (h16 : Equation16 G) (h263 : Equation263 G) : Equation221 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation26_49_implies_Equation261 (G : Type*) [Magma G] (h26 : Equation26 G) (h49 : Equation49 G) : Equation261 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h26 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h26 X0 X1]
  intro x y
  conv => enter [1]; rw [h26 x y]
  conv => enter [1, 1]; rw [l1 x y]

theorem Equation16_260_implies_Equation65 (G : Type*) [Magma G] (h16 : Equation16 G) (h260 : Equation260 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h16 X0 X1]
  intro x y
  conv => enter [1]; rw [h16 x y]
  conv => enter [1, 2]; rw [l1 y x]

theorem Equation3_381_implies_Equation266 (G : Type*) [Magma G] (h3 : Equation3 G) (h381 : Equation381 G) : Equation266 G := by
  intro x y z
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h381 x x y]
  conv => enter [1]; rw [h381 (x ◇ y) x z]

theorem Equation3_329_implies_Equation58 (G : Type*) [Magma G] (h3 : Equation3 G) (h329 : Equation329 G) : Equation58 G := by
  intro x y z
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [h329 x x z]
  conv => enter [1]; rw [h329 x (z ◇ x) y]

theorem Equation221_266_implies_Equation5 (G : Type*) [Magma G] (h221 : Equation221 G) (h266 : Equation266 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h266 X1 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation58_105_implies_Equation4 (G : Type*) [Magma G] (h58 : Equation58 G) (h105 : Equation105 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h58 X1 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation224_333_implies_Equation238 (G : Type*) [Magma G] (h224 : Equation224 G) (h333 : Equation333 G) : Equation238 G := by
  have l0 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 1, 2]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h224 X1 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation106_377_implies_Equation103 (G : Type*) [Magma G] (h106 : Equation106 G) (h377 : Equation377 G) : Equation103 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 1]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h106 X1 (X1 ◇ X0) X2]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

theorem Equation159_224_implies_Equation5 (G : Type*) [Magma G] (h159 : Equation159 G) (h224 : Equation224 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h224 X0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation106_159_implies_Equation4 (G : Type*) [Magma G] (h106 : Equation106 G) (h159 : Equation159 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h106 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation3_14_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h14 : Equation14 G) : Equation66 G := by
  intro x y
  conv => enter [1]; rw [h14 x y]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation162_266_implies_Equation381 (G : Type*) [Magma G] (h162 : Equation162 G) (h266 : Equation266 G) : Equation381 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h162 (X1 ◇ X0) X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h162 X0 X1 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X0]
    conv => enter [1, 1]; rw [← h266 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation58_162_implies_Equation329 (G : Type*) [Magma G] (h58 : Equation58 G) (h162 : Equation162 G) : Equation329 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h162 (X0 ◇ X1) (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h162 X0 X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X2 ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h58 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation3_10_25_58_266_implies_Equation162 (G : Type*) [Magma G] (h3 : Equation3 G) (h10 : Equation10 G) (h25 : Equation25 G) (h58 : Equation58 G) (h266 : Equation266 G) : Equation162 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h58 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h266 (X0 ◇ X1) X0 X2]
    conv => enter [1, 1, 1]; rw [← h25 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h266 (X0 ◇ X1) X2 X1]
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X2) X1 X0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l2 X0 X2 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [l3 X1 X0 (X2 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 x y x]
  conv => enter [1]; rw [l4 (x ◇ y) x z]

theorem Equation66_151_159_273_implies_Equation75 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h159 : Equation159 G) (h273 : Equation273 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [l1 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 ((X1 ◇ X2) ◇ X1) X2]
    conv => enter [1]; rw [l0 X2 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 (X0 ◇ (X0 ◇ X1)) X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation159_206_209_implies_Equation24 (G : Type*) [Magma G] (h159 : Equation159 G) (h206 : Equation206 G) (h209 : Equation209 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h209 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h209 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← h206 X0 X1]
    conv => enter [1, 2, 2]; rw [← h206 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l5 (X1 ◇ X0) (X0 ◇ X1)]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [← h159 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← l2 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l8 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← l8 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l5 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [l5 (X0 ◇ X1) X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ (X1 ◇ X0)) X0]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l14 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l17 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l17 X0 (X1 ◇ X0)]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation117_124_159_implies_Equation13 (G : Type*) [Magma G] (h117 : Equation117 G) (h124 : Equation124 G) (h159 : Equation159 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h117 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h159 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2]; rw [← h117 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X1 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h124 X0 X1]
    conv => enter [1, 1, 1]; rw [← h124 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l5 (((X1 ◇ X0) ◇ X1) ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l5 (X1 ◇ X0) (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [← h159 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l8 X1 (X0 ◇ ((X0 ◇ X1) ◇ X0))]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← l8 X1 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1, 1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l4 (X1 ◇ X0) X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l5 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2]; rw [l5 X1 (X1 ◇ X0)]
  have l15 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l5 X0 ((X0 ◇ X1) ◇ X0)]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 1]; rw [← l9 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l17 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2]; rw [← l17 X0 (X0 ◇ X1)]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [l16 X1 X0]
  intro x y
  conv => enter [1]; rw [← l20 y x]

theorem Equation261_308_325_implies_Equation258 (G : Type*) [Magma G] (h261 : Equation261 G) (h308 : Equation308 G) (h325 : Equation325 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h308 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation65_364_385_implies_Equation72 (G : Type*) [Magma G] (h65 : Equation65 G) (h364 : Equation364 G) (h385 : Equation385 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h364 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation260_261_326_implies_Equation256 (G : Type*) [Magma G] (h260 : Equation260 G) (h261 : Equation261 G) (h326 : Equation326 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l2 X0 X2]
    conv => enter [1]; rw [← h326 X1 ((X0 ◇ X2) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 2]; rw [← l3 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← h260 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 ((X0 ◇ X1) ◇ X0) X2]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 x x y]

theorem Equation49_65_375_implies_Equation62 (G : Type*) [Magma G] (h49 : Equation49 G) (h65 : Equation65 G) (h375 : Equation375 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l2 X0 X2]
    conv => enter [1]; rw [← h375 (X0 ◇ (X2 ◇ X0)) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2, 1]; rw [← l3 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h49 X0 X1]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x x]

theorem Equation260_261_308_implies_Equation256 (G : Type*) [Magma G] (h260 : Equation260 G) (h261 : Equation261 G) (h308 : Equation308 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h308 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X0) X2]
    conv => enter [1, 1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 1, 2, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ X0))]
    conv => enter [1]; rw [← l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l10 (X0 ◇ X1) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l15 x y]

theorem Equation49_65_364_implies_Equation62 (G : Type*) [Magma G] (h49 : Equation49 G) (h65 : Equation65 G) (h364 : Equation364 G) : Equation62 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h364 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X2 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 1, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1 ((X0 ◇ (X1 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [← l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l10 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [l10 (X1 ◇ X0) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l11 X1 X0]
    conv => enter [1]; rw [← l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l15 y x]

theorem Equation221_274_implies_Equation2 (G : Type*) [Magma G] (h221 : Equation221 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h274 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1, 2, 2]; rw [← h274 X0 X1]
    conv => enter [1, 2, 2]; rw [← h274 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h274 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1, 2]; rw [← h274 X1 X0]
    conv => enter [1, 2]; rw [← h274 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h274 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation73_105_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h105 : Equation105 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h73 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 1, 1]; rw [← h73 X0 X1]
    conv => enter [1, 1, 1]; rw [← h73 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h73 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X1 ◇ X0)) ◇ X1)]
    conv => enter [1, 2, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2, 1]; rw [← h73 X1 X0]
    conv => enter [1, 1]; rw [← h73 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation209_274_implies_Equation118 (G : Type*) [Magma G] (h209 : Equation209 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 ((X0 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h274 ((X0 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h274 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h209 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [← l4 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [l8 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2]; rw [l9 y x]

theorem Equation209_274_implies_Equation222 (G : Type*) [Magma G] (h209 : Equation209 G) (h274 : Equation274 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 ((X0 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h274 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 (x ◇ y) y]

theorem Equation73_117_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h117 : Equation117 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ (X1 ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [l3 (y ◇ x) y]

theorem Equation205_274_implies_Equation2 (G : Type*) [Magma G] (h205 : Equation205 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h274 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h274 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation73_104_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h104 : Equation104 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h73 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h73 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation151_212_274_implies_Equation66 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h274 : Equation274 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X1) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h212 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 ((X1 ◇ X1) ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X1 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l12 (X0 ◇ X0) X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X0) (X1 ◇ ((X0 ◇ X1) ◇ X0))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l15 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [l12 X1 X0]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l13 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← l5 ((X1 ◇ X1) ◇ X0) X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1]; rw [l19 (X1 ◇ X1) X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X1 X0]
    conv => enter [1]; rw [l21 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l23 X1 X0]
  have l26 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 ((X0 ◇ X0) ◇ X1) ((X1 ◇ X0) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [l10 X1 X0]
  have l27 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [← l24 X0 (X1 ◇ X0)]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l27 X0 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [l19 (X0 ◇ X0) X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2, 2]; rw [← h151 X0]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) (X1 ◇ X1)]
  have l32 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l7 X1 X0]
    conv => enter [1, 2, 1]; rw [l7 X1 X0]
  have l33 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l25 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1, 1]; rw [← h151 X1]
  have l35 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1]; rw [← l30 X0 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))]
  have l36 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 2]; rw [l19 ((X0 ◇ X0) ◇ X1) (X1 ◇ X0)]
  have l37 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 (X0 ◇ X0) X1]
  have l38 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h151 X0]
  have l39 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1, 2, 2]; rw [← l34 X1 (X1 ◇ X0)]
  have l40 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 X1 X0]
  have l41 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l42 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l41 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l43 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l42 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l13 X1 X0]
  intro x y
  conv => enter [1]; rw [← l43 y x]

theorem Equation151_212_274_implies_Equation73 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X1) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h212 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 ((X1 ◇ X1) ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X1 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l12 (X0 ◇ X0) X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X0) (X1 ◇ ((X0 ◇ X1) ◇ X0))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l15 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [l12 X1 X0]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l13 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← l5 ((X1 ◇ X1) ◇ X0) X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1]; rw [l19 (X1 ◇ X1) X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X1 X0]
    conv => enter [1]; rw [l21 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l23 X1 X0]
  have l26 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 ((X0 ◇ X0) ◇ X1) ((X1 ◇ X0) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [l10 X1 X0]
  have l27 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [← l24 X0 (X1 ◇ X0)]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l27 X0 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [l19 (X0 ◇ X0) X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2, 2]; rw [← h151 X0]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) (X1 ◇ X1)]
  have l32 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l7 X1 X0]
    conv => enter [1, 2, 1]; rw [l7 X1 X0]
  have l33 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l25 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) X0]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1, 1]; rw [← h151 X1]
  have l36 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 X1 X0]
    conv => enter [1]; rw [← l30 X0 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))]
  have l37 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1, 2]; rw [l19 ((X0 ◇ X0) ◇ X1) (X1 ◇ X0)]
  have l38 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 (X0 ◇ X0) X1]
  have l39 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h151 X0]
  have l40 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2]; rw [← l35 X1 (X1 ◇ X0)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 X1 X0]
  have l42 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l41 X1 X0]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l43 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l42 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l44 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l33 X1 X0]
  intro x y
  conv => enter [1]; rw [← l44 y x]

theorem Equation151_212_274_implies_Equation118 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X1) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h212 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [h274 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 ((X1 ◇ X1) ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X1 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l12 (X0 ◇ X0) X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X0) (X1 ◇ ((X0 ◇ X1) ◇ X0))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l15 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [l12 X1 X0]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l13 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← l5 ((X1 ◇ X1) ◇ X0) X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1]; rw [l19 (X1 ◇ X1) X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X1 X0]
    conv => enter [1]; rw [l21 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X1]
    conv => enter [1]; rw [← l23 X1 X0]
  have l26 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 ((X0 ◇ X0) ◇ X1) ((X1 ◇ X0) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [l10 X1 X0]
  have l27 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [← l24 X0 (X1 ◇ X0)]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l27 X0 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [l19 (X0 ◇ X0) X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2, 2]; rw [← h151 X0]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) (X1 ◇ X1)]
  have l32 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l7 X1 X0]
    conv => enter [1, 2, 1]; rw [l7 X1 X0]
  have l33 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l25 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) X0]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1, 1]; rw [← h151 X1]
  have l36 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 X1 X0]
    conv => enter [1]; rw [← l30 X0 (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))]
  have l37 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1, 2]; rw [l19 ((X0 ◇ X0) ◇ X1) (X1 ◇ X0)]
  have l38 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 (X0 ◇ X0) X1]
  have l39 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h151 X0]
  have l40 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2]; rw [← l35 X1 (X1 ◇ X0)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l40 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l19 X1 X0]
  have l42 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l41 X1 X0]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l43 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l42 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l44 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l33 X1 X0]
  intro x y
  conv => enter [1]; rw [← l44 y x]
  conv => enter [1, 2]; rw [l43 y (x ◇ y)]

theorem Equation73_127_151_implies_Equation66 (G : Type*) [Magma G] (h73 : Equation73 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h73 X1 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h127 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h127 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l4 (X1 ◇ X1) X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h151 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l12 X1 (X0 ◇ X0)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← l4 ((X0 ◇ (X1 ◇ X0)) ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X1 ◇ X0)) ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l16 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← l15 X0 X1]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 1, 1]; rw [← l4 X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l12 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l13 X0 X1]
    conv => enter [1, 2, 1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [← l5 (X0 ◇ (X1 ◇ X1)) X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [l19 X0 (X1 ◇ X1)]
  have l24 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l19 X0 X1]
    conv => enter [1]; rw [l21 X0 X1]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h151 X1]
    conv => enter [1]; rw [← l23 X0 X1]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ X0)) ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 1]; rw [l10 X1 X0]
    conv => enter [1, 1]; rw [l10 X1 X0]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1]; rw [← l24 (X0 ◇ X1) X0]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l27 X1 X0]
  have l29 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1]; rw [l19 X1 (X0 ◇ X0)]
  have l30 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l29 X1 X0]
    conv => enter [1, 1, 1]; rw [← h151 X0]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l7 (X1 ◇ X1) (X1 ◇ X0)]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1, 2]; rw [l7 X0 X1]
    conv => enter [1, 1, 2]; rw [l7 X0 X1]
  have l34 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1]; rw [← l25 X0 ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l35 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2]; rw [← h151 X1]
  have l36 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1]; rw [← l30 ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) X0]
  have l37 : ∀ X0 X1 : G, (X0 ◇ X1) = (((((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l36 X0 X1]
    conv => enter [1, 1]; rw [l19 (X0 ◇ X1) (X1 ◇ (X0 ◇ X0))]
  have l38 : ∀ X0 X1 : G, (X0 ◇ X1) = (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l37 X0 X1]
    conv => enter [1, 1, 1, 1]; rw [l19 X1 (X0 ◇ X0)]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l38 X0 X1]
    conv => enter [1, 1, 1, 1, 1, 1]; rw [← h151 X0]
  have l40 : ∀ X0 X1 : G, (X0 ◇ X1) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l39 X0 X1]
    conv => enter [1, 1, 1]; rw [← l35 (X0 ◇ X1) X1]
  have l41 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l40 X0 X1]
    conv => enter [1, 1, 1, 1]; rw [l19 X0 X1]
  have l42 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l41 X0 X1]
    conv => enter [1, 1, 1]; rw [← l20 X0 X1]
  have l43 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l42 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l43 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l44 y x]
  conv => enter [1]; rw [l32 y x]

theorem Equation73_127_151_implies_Equation118 (G : Type*) [Magma G] (h73 : Equation73 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h73 X1 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h127 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h127 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l4 (X1 ◇ X1) X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h151 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [h73 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l12 X1 (X0 ◇ X0)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X1 ◇ X0)) ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l15 X0 X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l12 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l13 X0 X1]
    conv => enter [1, 2, 1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [← l5 (X0 ◇ (X1 ◇ X1)) X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [l17 X0 (X1 ◇ X1)]
  have l21 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [l18 X0 X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h151 X1]
    conv => enter [1]; rw [← l20 X0 X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ X0)) ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 1]; rw [l10 X1 X0]
    conv => enter [1, 1]; rw [l10 X1 X0]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [← l21 (X0 ◇ X1) X0]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l14 X1 X0]
    conv => enter [1]; rw [← l24 X1 X0]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [l17 X1 (X0 ◇ X0)]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1, 1, 1]; rw [← h151 X0]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l29 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l22 X0 X1]
    conv => enter [1]; rw [l28 X1 X0]
  intro x y
  conv => enter [1]; rw [← l29 x y]
  conv => enter [1]; rw [← l27 y (x ◇ y)]
  conv => enter [1]; rw [l4 y (x ◇ y)]

theorem Equation167_274_implies_Equation118 (G : Type*) [Magma G] (h167 : Equation167 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h274 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1, 2, 1]; rw [← h167 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h274 ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [l7 (X0 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l7 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2, 2]; rw [← l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [← h167 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1, 2]; rw [l15 y x]

theorem Equation167_274_implies_Equation222 (G : Type*) [Magma G] (h167 : Equation167 G) (h274 : Equation274 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h274 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1, 2, 1]; rw [← h167 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h274 ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [l7 (X0 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l7 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2, 2]; rw [← l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [← h167 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1, 2]; rw [l15 y x]
  conv => enter [1]; rw [← l7 y (x ◇ y)]

theorem Equation73_167_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h167 : Equation167 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h73 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2, 1, 2]; rw [← h167 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h73 (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1]; rw [l7 (X1 ◇ X0) ((X0 ◇ X1) ◇ X0)]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1, 1]; rw [← l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [← h167 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l16 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [← l17 x y]
  conv => enter [1, 1]; rw [l15 x y]
  conv => enter [1]; rw [← l7 y (y ◇ x)]

theorem Equation167_221_255_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h221 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h255 X0]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← l0 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l4 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1]; rw [← h255 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2, 2]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2]; rw [← h221 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [l10 (X0 ◇ X1) X1]
  have l12 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l11 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation47_105_167_implies_Equation2 (G : Type*) [Magma G] (h47 : Equation47 G) (h105 : Equation105 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← h105 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1, 1, 1]; rw [← h47 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l4 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [← h47 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1, 1]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 1]; rw [← h105 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [l10 (X1 ◇ X0) X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l11 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation152_274_implies_Equation2 (G : Type*) [Magma G] (h152 : Equation152 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h152 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h152 X0 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h274 ((X0 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h274 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h274 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1, 1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation73_166_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h166 : Equation166 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h166 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h166 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h73 (X1 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h73 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h73 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h73 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1, 2, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation127_274_implies_Equation118 (G : Type*) [Magma G] (h127 : Equation127 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h127 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h127 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation127_274_implies_Equation222 (G : Type*) [Magma G] (h127 : Equation127 G) (h274 : Equation274 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h127 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h127 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [← l2 y (x ◇ y)]

theorem Equation73_212_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h212 : Equation212 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h212 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h212 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [← l2 y (y ◇ x)]

theorem Equation229_274_implies_Equation73 (G : Type*) [Magma G] (h229 : Equation229 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h229 X1 X0]
    conv => enter [1]; rw [← h274 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation229_274_implies_Equation118 (G : Type*) [Magma G] (h229 : Equation229 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h229 X1 X0]
    conv => enter [1]; rw [← h274 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [l0 y (x ◇ y)]

theorem Equation73_118_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h118 : Equation118 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h118 X1 X0]
    conv => enter [1]; rw [← h73 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1]; rw [l0 ((y ◇ x) ◇ y) y]

theorem Equation151_212_229_implies_Equation73 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation118_127_151_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 1]; rw [l3 y x]

theorem Equation118_151_212_implies_Equation66 (G : Type*) [Magma G] (h118 : Equation118 G) (h151 : Equation151 G) (h212 : Equation212 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h118 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h212 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h212 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 (((X1 ◇ X0) ◇ X0) ◇ X1) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l5 X0 (((X1 ◇ X0) ◇ X0) ◇ X1)]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
  have l12 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 1]; rw [l5 X1 X0]
    conv => enter [1, 2, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l8 (X0 ◇ X0) X1]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X1 X0]
  have l14 : ∀ X1 X0 : G, ((((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l13 (((X1 ◇ X0) ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l15 (X1 ◇ X0) X1]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1, 1]; rw [l16 (y ◇ y) x]
  conv => enter [1]; rw [l16 (x ◇ (y ◇ y)) y]

theorem Equation118_274_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h274 : Equation274 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  intro x y
  conv => enter [1]; rw [h118 x y]
  conv => enter [1]; rw [← l0 y (x ◇ y)]

theorem Equation73_229_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h229 : Equation229 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  intro x y
  conv => enter [1]; rw [h229 x y]
  conv => enter [1]; rw [← l0 y (y ◇ x)]

theorem Equation73_274_implies_Equation118 (G : Type*) [Magma G] (h73 : Equation73 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h73 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h274 X1 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [h73 x y]
  conv => enter [1, 2]; rw [l1 y (x ◇ y)]

theorem Equation66_151_274_implies_Equation73 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h66 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h66 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h151 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h66 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation66_73_151_281_implies_Equation118 (G : Type*) [Magma G] (h66 : Equation66 G) (h73 : Equation73 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h281 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [← h73 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h281 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 (X1 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1, 1]; rw [← h151 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X0 ◇ X1))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l11 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l9 (X0 ◇ X1) X1]
    conv => enter [1, 1, 2]; rw [l9 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [← h281 X1 ((X1 ◇ X0) ◇ X0)]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [← l13 x y]
  conv => enter [1]; rw [← l4 y (x ◇ y)]

theorem Equation66_151_229_implies_Equation73 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h66 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h66 ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 (X1 ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h66 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X0 (X1 ◇ X1)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X1) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l9 X1 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l9 (X1 ◇ X0) X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l9 X1 (X1 ◇ (X0 ◇ X1))]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l13 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X1) X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 (X0 ◇ (X1 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← l15 X0 (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h66 (X0 ◇ X1) X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l19 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l17 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l19 (X0 ◇ (X1 ◇ X1)) (X1 ◇ X0)]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l22 X0 X1]
    conv => enter [1]; rw [l21 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l19 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l24 X0 X1]
  intro x y
  conv => enter [1]; rw [← l25 y x]

theorem Equation66_118_151_281_implies_Equation73 (G : Type*) [Magma G] (h66 : Equation66 G) (h118 : Equation118 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h281 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h281 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h66 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h281 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l1 (X1 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 1, 1]; rw [l0 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l11 X0 (X1 ◇ X0)]
  have l13 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l11 X0 X1]
    conv => enter [1, 1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l11 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [l11 X1 (X0 ◇ X1)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [l11 ((X1 ◇ X0) ◇ X1) X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l16 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 1]; rw [← l1 X1 (X1 ◇ X0)]
  have l20 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 (X0 ◇ X1) ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← l18 (X1 ◇ X0) X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← h281 (X1 ◇ X0) X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l24 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l21 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l25 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l22 ((X1 ◇ X1) ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l20 X0 X1]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l22 X1 (X0 ◇ X1)]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 1]; rw [l24 X1 X0]
  have l28 : ∀ X1 X0 : G, (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l24 X0 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [l22 (X0 ◇ X1) ((X1 ◇ X1) ◇ X0)]
  have l30 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l29 X0 X1]
    conv => enter [1]; rw [l25 X1 X0]
  have l31 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l30 X0 X1]
  have l32 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l22 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l31 X0 X1]
  have l33 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l22 X1 X0]
    conv => enter [1]; rw [l32 X0 X1]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l26 X0 X1]
  have l35 : ∀ X1 X0 : G, (X1 ◇ X1) = (((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← l26 X1 X0]
  have l36 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 1, 1]; rw [← l29 X0 X1]
  have l37 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l27 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1, 1]; rw [← l26 X1 X0]
  have l38 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l27 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1, 1]; rw [← l18 X1 X0]
  have l39 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1, 1, 1]; rw [← l36 X0 X1]
  have l40 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l37 X0 X1]
    conv => enter [1, 1, 1]; rw [← l29 X0 X1]
  have l41 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l11 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l24 X1 X0]
  have l42 : ∀ X1 X0 X2 : G, (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1, 1]; rw [← l39 X0 X1]
    conv => enter [1]; rw [← h281 X2 (X0 ◇ X1)]
  have l43 : ∀ X2 X1 X0 : G, (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← l39 X0 X1]
    conv => enter [1]; rw [l34 X2 (X0 ◇ X1)]
  have l44 : ∀ X1 X0 X2 : G, (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1, 1]; rw [← l40 X1 X0]
    conv => enter [1]; rw [← h281 X2 (X1 ◇ X0)]
  have l45 : ∀ X1 X0 X2 : G, (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = (X2 ◇ (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 1, 1]; rw [← l40 X1 X0]
    conv => enter [1, 2]; rw [← l40 X1 X0]
    conv => enter [1]; rw [l41 (X1 ◇ X0) (X1 ◇ X0) X2]
    conv => enter [1, 2, 1, 1]; rw [l40 X1 X0]
  have l46 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← l44 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l45 X1 X0 X2]
  have l47 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = ((((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l46 X2 X1 X0]
    conv => enter [1]; rw [l43 ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) X1 X0]
  have l48 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l47 X2 X1 X0]
    conv => enter [1, 1]; rw [l42 X1 X0 X2]
  intro x y
  conv => enter [1]; rw [← l33 x y]
  conv => enter [1]; rw [l22 ((x ◇ y) ◇ y) y]
  conv => enter [1]; rw [l48 y (x ◇ y) y]

theorem Equation43_274_implies_Equation73 (G : Type*) [Magma G] (h43 : Equation43 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation43_73_implies_Equation118 (G : Type*) [Magma G] (h43 : Equation43 G) (h73 : Equation73 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h73 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [h43 ((x ◇ y) ◇ y) y]

theorem Equation274_385_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_325_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h73 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_335_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h73 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 1]; rw [h335 x y]
  conv => enter [1]; rw [l0 y (y ◇ x)]

theorem Equation274_378_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h378 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h378 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_323_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h73 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h323 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_333_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h73 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation274_335_implies_Equation118 (G : Type*) [Magma G] (h274 : Equation274 G) (h335 : Equation335 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation73_384_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h384 : Equation384 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1]; rw [← l0 y (y ◇ x)]

theorem Equation274_333_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h333 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation73_377_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h377 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h73 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h73 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation274_325_375_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h325 : Equation325 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h325 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation73_326_385_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h326 : Equation326 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h73 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation274_323_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h323 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_378_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h73 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h378 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h73 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation271_274_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation63_73_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h73 : Equation73 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 (X1 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation270_274_implies_Equation2 (G : Type*) [Magma G] (h270 : Equation270 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h270 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation48_73_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h73 : Equation73 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h48 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_263_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h274 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h3 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_55_73_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h73 : Equation73 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h73 X0 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation118_325_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation229_384_implies_Equation73 (G : Type*) [Magma G] (h229 : Equation229 G) (h384 : Equation384 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h229 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation118_335_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h335 : Equation335 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 1]; rw [l0 y x]

theorem Equation118_323_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h323 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation118_333_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h333 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h333 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation118_384_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [h384 y (y ◇ x)]
  conv => enter [1, 1]; rw [l0 y x]

theorem Equation118_326_375_377_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h326 : Equation326 G) (h375 : Equation375 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h377 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h326 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation118_385_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h118 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation118_378_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h378 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation229_273_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation53_118_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← l0 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_229_271_375_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h229 : Equation229 G) (h271 : Equation271 G) (h375 : Equation375 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h229 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1, 1, 1, 1]; rw [← h375 X0 X1]
    conv => enter [1, 2, 1]; rw [← h375 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_63_118_326_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h118 : Equation118 G) (h326 : Equation326 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← h326 X1 X0]
    conv => enter [1, 1, 2]; rw [← h326 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 1]; rw [l6 y x]

theorem Equation229_270_326_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h270 : Equation270 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h270 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation48_118_375_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h118 : Equation118 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h48 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_229_263_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h229 : Equation229 G) (h263 : Equation263 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h229 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [← l5 y (x ◇ y)]

theorem Equation3_55_118_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h118 : Equation118 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h118 X0 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1]; rw [← l5 (y ◇ x) y]
  conv => enter [1, 1]; rw [l6 y x]

theorem Equation3_229_261_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h229 : Equation229 G) (h261 : Equation261 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_65_118_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h118 : Equation118 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ ((X0 ◇ X0) ◇ X1))]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation229_260_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h260 : Equation260 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation49_118_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

end Order3
