import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation53_104_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h104 : Equation104 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation3_205_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h205 : Equation205 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation3_63_104_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h104 : Equation104 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h63 X0 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation205_228_263_implies_Equation5 (G : Type*) [Magma G] (h205 : Equation205 G) (h228 : Equation228 G) (h263 : Equation263 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h205 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h263 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation55_102_104_implies_Equation4 (G : Type*) [Magma G] (h55 : Equation55 G) (h102 : Equation102 G) (h104 : Equation104 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h55 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation167_385_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h385 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation167_325_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h325 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation167_384_implies_Equation118 (G : Type*) [Magma G] (h167 : Equation167 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h384 y x]

theorem Equation167_384_implies_Equation222 (G : Type*) [Magma G] (h167 : Equation167 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [h384 y x]
  conv => enter [1]; rw [l1 y (x ◇ y)]

theorem Equation3_167_384_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h384 : Equation384 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 y (x ◇ x)]

theorem Equation167_335_implies_Equation73 (G : Type*) [Magma G] (h167 : Equation167 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [h335 (x ◇ y) y]

theorem Equation167_335_implies_Equation125 (G : Type*) [Magma G] (h167 : Equation167 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [h335 x y]
  conv => enter [1]; rw [l1 y (y ◇ x)]

theorem Equation3_167_335_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h335 : Equation335 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 (x ◇ x) y]

theorem Equation167_378_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h167 X0 X1]
    conv => enter [1]; rw [← h378 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h378 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h378 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation167_323_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h167 X0 X1]
    conv => enter [1]; rw [← h323 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h323 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h323 (X1 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation167_377_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h167 X0 X1]
    conv => enter [1]; rw [← h377 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation167_333_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h167 X0 X1]
    conv => enter [1]; rw [← h333 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_167_270_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h270 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2]; rw [← h270 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ X0)]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← l8 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [← h167 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l14 X1 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3_48_167_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h48 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← l8 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3_167_263_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h263 : Equation263 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [l5 (x ◇ y) y]

theorem Equation3_167_263_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h263 : Equation263 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2]; rw [l7 x y]

theorem Equation3_167_263_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h263 : Equation263 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_55_167_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h167 : Equation167 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1, 2]; rw [l5 y x]

theorem Equation3_55_167_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h167 : Equation167 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]
  conv => enter [1, 1]; rw [l7 x y]

theorem Equation3_55_167_implies_Equation384 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h167 : Equation167 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation167_228_implies_Equation118 (G : Type*) [Magma G] (h167 : Equation167 G) (h228 : Equation228 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h228 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← h167 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l6 y x]

theorem Equation167_228_implies_Equation222 (G : Type*) [Magma G] (h167 : Equation167 G) (h228 : Equation228 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h228 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← h167 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l6 y x]
  conv => enter [1]; rw [l7 y (x ◇ y)]

theorem Equation167_228_implies_Equation384 (G : Type*) [Magma G] (h167 : Equation167 G) (h228 : Equation228 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h167 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h228 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← h167 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation102_167_implies_Equation73 (G : Type*) [Magma G] (h102 : Equation102 G) (h167 : Equation167 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h102 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [l6 (x ◇ y) y]

theorem Equation102_167_implies_Equation125 (G : Type*) [Magma G] (h102 : Equation102 G) (h167 : Equation167 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h102 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l6 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [l6 x y]
  conv => enter [1]; rw [l7 y (y ◇ x)]

theorem Equation102_167_implies_Equation335 (G : Type*) [Magma G] (h102 : Equation102 G) (h167 : Equation167 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h167 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1]; rw [← h102 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation167_209_264_375_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h209 : Equation209 G) (h264 : Equation264 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← l2 X1 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [l1 (X1 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation75_117_167_326_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h117 : Equation117 G) (h167 : Equation167 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1]; rw [l1 (X1 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation167_208_implies_Equation2 (G : Type*) [Magma G] (h167 : Equation167 G) (h208 : Equation208 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h208 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1, 1, 1]; rw [h208 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h208 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation101_167_implies_Equation2 (G : Type*) [Magma G] (h101 : Equation101 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h101 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [← h101 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1, 2, 2]; rw [h101 X0 X1]
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h101 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation159_384_implies_Equation14 (G : Type*) [Magma G] (h159 : Equation159 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation3_159_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_159_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 y (x ◇ x)]

theorem Equation159_335_implies_Equation14 (G : Type*) [Magma G] (h159 : Equation159 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_159_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_159_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h159 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation159_377_implies_Equation9 (G : Type*) [Magma G] (h159 : Equation159 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← h377 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation159_333_implies_Equation28 (G : Type*) [Magma G] (h159 : Equation159 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← h333 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation159_271_implies_Equation73 (G : Type*) [Magma G] (h159 : Equation159 G) (h271 : Equation271 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h159 X1 X0]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h271 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 ((X1 ◇ X0) ◇ X1)]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation159_271_implies_Equation125 (G : Type*) [Magma G] (h159 : Equation159 G) (h271 : Equation271 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h159 X1 X0]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h271 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation63_159_implies_Equation118 (G : Type*) [Magma G] (h63 : Equation63 G) (h159 : Equation159 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h63 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h159 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h63 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 (X1 ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1]; rw [l9 y (x ◇ y)]

theorem Equation63_159_implies_Equation222 (G : Type*) [Magma G] (h63 : Equation63 G) (h159 : Equation159 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h63 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h159 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h63 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation3_159_221_270_implies_Equation208 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h221 : Equation221 G) (h270 : Equation270 G) : Equation208 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1, 1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_48_105_159_implies_Equation101 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h105 : Equation105 G) (h159 : Equation159 G) : Equation101 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1, 2, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_159_221_260_implies_Equation205 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h221 : Equation221 G) (h260 : Equation260 G) : Equation205 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h260 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h159 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h221 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [← h3 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h221 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_49_105_159_implies_Equation104 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h105 : Equation105 G) (h159 : Equation159 G) : Equation104 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h49 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h159 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h105 ((sK1 ◇ sK0) ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [← h3 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h105 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation159_209_264_implies_Equation4 (G : Type*) [Magma G] (h159 : Equation159 G) (h209 : Equation209 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation75_117_159_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h117 : Equation117 G) (h159 : Equation159 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation159_209_261_implies_Equation48 (G : Type*) [Magma G] (h159 : Equation159 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation48 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h261 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← h159 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← l6 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l6 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [← l8 X0 X1]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X1 (X0 ◇ X1)]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1]; rw [← l14 X1 (X0 ◇ X1)]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X0 X1]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l19 X1 X0]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l21 X0 X1]
  intro x y
  conv => enter [1]; rw [← l22 x y]

theorem Equation159_209_261_implies_Equation102 (G : Type*) [Magma G] (h159 : Equation159 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation102 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h261 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← h159 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← l6 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l6 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [← l8 X0 X1]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X1 (X0 ◇ X1)]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1]; rw [← l14 X1 (X0 ◇ X1)]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1, 2]; rw [← l13 X0 X1]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l19 X1 X0]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l21 X0 X1]
  intro x y
  conv => enter [1]; rw [← l22 x y]
  conv => enter [1, 2]; rw [l13 x y]

theorem Equation65_117_159_implies_Equation228 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h159 : Equation159 G) : Equation228 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h159 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l6 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ X0)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l6 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [← l6 X0 (X0 ◇ X1)]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l8 X1 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← l8 X1 X0]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 2, 1]; rw [← l13 (X1 ◇ X0) X1]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2]; rw [← l14 X1 (X1 ◇ X0)]
  have l18 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2, 1]; rw [← l13 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l19 X0 X1]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l20 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l22 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l13 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l21 X1 X0]
  intro x y
  conv => enter [1]; rw [← l22 y x]
  conv => enter [1, 1]; rw [l13 y x]

theorem Equation65_117_159_implies_Equation270 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h159 : Equation159 G) : Equation270 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h159 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l6 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ X0)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l6 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [← l6 X0 (X0 ◇ X1)]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l8 X1 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← l8 X1 X0]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 2, 1]; rw [← l13 (X1 ◇ X0) X1]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2]; rw [← l14 X1 (X1 ◇ X0)]
  have l18 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2, 1]; rw [← l13 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l18 X1 X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l19 X0 X1]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l20 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l22 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l13 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l21 X1 X0]
  intro x y
  conv => enter [1]; rw [← l22 y x]

theorem Equation159_208_228_implies_Equation270 (G : Type*) [Magma G] (h159 : Equation159 G) (h208 : Equation208 G) (h228 : Equation228 G) : Equation270 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation101_102_159_implies_Equation48 (G : Type*) [Magma G] (h101 : Equation101 G) (h102 : Equation102 G) (h159 : Equation159 G) : Equation48 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h101 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h101 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation159_205_228_implies_Equation260 (G : Type*) [Magma G] (h159 : Equation159 G) (h205 : Equation205 G) (h228 : Equation228 G) : Equation260 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h205 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← h159 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h205 ((sK0 ◇ sK1) ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h228 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation102_104_159_implies_Equation49 (G : Type*) [Magma G] (h102 : Equation102 G) (h104 : Equation104 G) (h159 : Equation159 G) : Equation49 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h104 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← h159 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h104 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h102 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation124_271_326_implies_Equation332 (G : Type*) [Magma G] (h124 : Equation124 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h124 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation124_271_implies_Equation63 (G : Type*) [Magma G] (h124 : Equation124 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h124 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation63_206_326_implies_Equation332 (G : Type*) [Magma G] (h63 : Equation63 G) (h206 : Equation206 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h206 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation63_206_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h206 : Equation206 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h206 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h206 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l4 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation124_270_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h270 : Equation270 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h124 X0 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation48_206_implies_Equation4 (G : Type*) [Magma G] (h48 : Equation48 G) (h206 : Equation206 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h206 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation124_264_implies_Equation14 (G : Type*) [Magma G] (h124 : Equation124 G) (h264 : Equation264 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation124_264_326_implies_Equation66 (G : Type*) [Magma G] (h124 : Equation124 G) (h264 : Equation264 G) (h326 : Equation326 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_124_264_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h264 : Equation264 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 y (x ◇ x)]

theorem Equation75_206_implies_Equation14 (G : Type*) [Magma G] (h75 : Equation75 G) (h206 : Equation206 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation75_206_326_implies_Equation66 (G : Type*) [Magma G] (h75 : Equation75 G) (h206 : Equation206 G) (h326 : Equation326 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_75_206_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h206 : Equation206 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 y (x ◇ x)]

theorem Equation124_263_375_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h263 : Equation263 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h124 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation55_206_326_implies_Equation4 (G : Type*) [Magma G] (h55 : Equation55 G) (h206 : Equation206 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h206 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation124_261_326_implies_Equation332 (G : Type*) [Magma G] (h124 : Equation124 G) (h261 : Equation261 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h261 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation124_261_implies_Equation63 (G : Type*) [Magma G] (h124 : Equation124 G) (h261 : Equation261 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h261 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation65_206_326_implies_Equation332 (G : Type*) [Magma G] (h65 : Equation65 G) (h206 : Equation206 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h65 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation65_206_implies_Equation63 (G : Type*) [Magma G] (h65 : Equation65 G) (h206 : Equation206 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h65 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [h206 x y]
  conv => enter [1]; rw [l1 (x ◇ (x ◇ y)) y]

theorem Equation124_260_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h260 : Equation260 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h260 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation49_206_implies_Equation4 (G : Type*) [Magma G] (h49 : Equation49 G) (h206 : Equation206 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation124_228_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h228 : Equation228 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h228 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h124 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation102_206_implies_Equation4 (G : Type*) [Magma G] (h102 : Equation102 G) (h206 : Equation206 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h102 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation124_209_326_implies_Equation332 (G : Type*) [Magma G] (h124 : Equation124 G) (h209 : Equation209 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h124 X0 X1]
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l5 (X0 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l5 X0 (X1 ◇ ((X0 ◇ X1) ◇ X1))]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X1 ((X0 ◇ X1) ◇ X1)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation124_209_implies_Equation63 (G : Type*) [Magma G] (h124 : Equation124 G) (h209 : Equation209 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h124 X0 X1]
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l5 (X0 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l5 X0 (X1 ◇ ((X0 ◇ X1) ◇ X1))]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X1 ((X0 ◇ X1) ◇ X1)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l13 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 y x]

theorem Equation117_206_326_implies_Equation332 (G : Type*) [Magma G] (h117 : Equation117 G) (h206 : Equation206 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h206 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ X1) ((X1 ◇ X0) ◇ X1)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [l5 (X1 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l5 X0 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 (X1 ◇ (X1 ◇ X0)) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation117_206_implies_Equation63 (G : Type*) [Magma G] (h117 : Equation117 G) (h206 : Equation206 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h206 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ X1) ((X1 ◇ X0) ◇ X1)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [l5 (X1 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l5 X0 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 (X1 ◇ (X1 ◇ X0)) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [h206 x y]
  conv => enter [1]; rw [l12 (x ◇ (x ◇ y)) y]

theorem Equation124_205_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h205 : Equation205 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h205 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation104_206_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h206 : Equation206 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation124_159_206_implies_Equation14 (G : Type*) [Magma G] (h124 : Equation124 G) (h159 : Equation159 G) (h206 : Equation206 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h206 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_124_159_206_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h159 : Equation159 G) (h206 : Equation206 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h206 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_124_159_206_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h159 : Equation159 G) (h206 : Equation206 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h206 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation118_274_385_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h274 : Equation274 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation229_325_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h229 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation274_384_implies_Equation167 (G : Type*) [Magma G] (h274 : Equation274 G) (h384 : Equation384 G) : Equation167 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation229_335_implies_Equation167 (G : Type*) [Magma G] (h229 : Equation229 G) (h335 : Equation335 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation118_222_274_378_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h222 : Equation222 G) (h274 : Equation274 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h378 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h222 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation229_323_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h323 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation274_377_implies_Equation2 (G : Type*) [Magma G] (h274 : Equation274 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation229_326_333_375_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h326 : Equation326 G) (h333 : Equation333 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h333 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h375 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h229 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation222_274_333_implies_Equation2 (G : Type*) [Magma G] (h222 : Equation222 G) (h274 : Equation274 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation229_377_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h377 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation222_274_325_implies_Equation2 (G : Type*) [Magma G] (h222 : Equation222 G) (h274 : Equation274 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation229_385_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation118_274_323_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h274 : Equation274 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h323 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation229_378_implies_Equation2 (G : Type*) [Magma G] (h229 : Equation229 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h378 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation118_222_271_274_326_375_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h222 : Equation222 G) (h271 : Equation271 G) (h274 : Equation274 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h222 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h118 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 ((X0 ◇ X1) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation63_73_125_229_326_375_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h73 : Equation73 G) (h125 : Equation125 G) (h229 : Equation229 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h125 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h229 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 ((X1 ◇ X1) ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_118_270_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h270 : Equation270 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h118 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_48_73_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h73 : Equation73 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h229 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_118_263_274_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h263 : Equation263 G) (h274 : Equation274 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h118 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_55_73_229_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h73 : Equation73 G) (h229 : Equation229 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h229 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_118_222_228_implies_Equation384 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h222 : Equation222 G) (h228 : Equation228 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h222 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_102_125_229_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h125 : Equation125 G) (h229 : Equation229 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h125 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_118_221_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h118 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h118 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_105_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h229 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation118_209_implies_Equation384 (G : Type*) [Magma G] (h118 : Equation118 G) (h209 : Equation209 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation117_229_implies_Equation335 (G : Type*) [Magma G] (h117 : Equation117 G) (h229 : Equation229 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation118_208_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h208 : Equation208 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h118 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation101_229_implies_Equation2 (G : Type*) [Magma G] (h101 : Equation101 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h101 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h229 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation118_206_222_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h206 : Equation206 G) (h222 : Equation222 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h222 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h222 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation124_229_implies_Equation2 (G : Type*) [Magma G] (h124 : Equation124 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h229 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h229 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation118_205_222_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h205 : Equation205 G) (h222 : Equation222 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h205 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h222 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation104_125_229_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h125 : Equation125 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h125 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation118_167_222_implies_Equation384 (G : Type*) [Magma G] (h118 : Equation118 G) (h167 : Equation167 G) (h222 : Equation222 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h167 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h167 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation167_229_implies_Equation335 (G : Type*) [Magma G] (h167 : Equation167 G) (h229 : Equation229 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2]; rw [← h229 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h167 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ (X0 ◇ X1))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h229 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l7 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l8 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation118_159_222_implies_Equation63 (G : Type*) [Magma G] (h118 : Equation118 G) (h159 : Equation159 G) (h222 : Equation222 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h159 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation159_229_implies_Equation271 (G : Type*) [Magma G] (h159 : Equation159 G) (h229 : Equation229 G) : Equation271 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2, 2]; rw [← h159 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← h229 X0 X1]
    conv => enter [1, 2]; rw [← h229 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 1, 1, 2]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 1, 1]; rw [← h229 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h229 (X0 ◇ X1) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h229 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [← l4 X0 X1]
    conv => enter [1, 2, 2]; rw [← l4 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l4 X0 X1]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [l11 (X0 ◇ X1) X0]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1, 1]; rw [← h229 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h229 X0 (X0 ◇ X1)]
  have l16 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2, 1]; rw [← l3 X1 X0]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 1]; rw [← l8 X0 X1]
  have l18 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [← h229 X0 (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l7 X1 X0]
  have l20 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l21 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l20 X0 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 2, 1]; rw [← l5 X1 X0]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [l21 X1 (X1 ◇ X0)]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l21 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (((X0 ◇ X1) ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l21 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1, 1]; rw [l15 X1 (((X0 ◇ X1) ◇ X0) ◇ X1)]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l23 X0 X1]
  have l28 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [← l21 X0 X1]
    conv => enter [1]; rw [← l26 X1 X0]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l28 X1 X0]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l10 X0 X1]
  have l31 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l18 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l10 X0 X1]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l31 X0 X1]
    conv => enter [1, 2]; rw [← l24 (X0 ◇ X1) ((X0 ◇ X1) ◇ X1)]
  have l33 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1]
    conv => enter [1, 2]; rw [l11 (X0 ◇ X1) X1]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1, 2]; rw [← l29 X1 (X0 ◇ X1)]
  have l35 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1, 2]; rw [l27 X1 X0]
  have l36 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l35 X0 X1]
    conv => enter [1, 1]; rw [← l30 X1 X0]
  have l37 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l27 X1 X0]
    conv => enter [1]; rw [l27 (X1 ◇ (X0 ◇ X1)) X1]
  have l38 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l24 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l37 X1 X0]
  have l39 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l36 X0 X1]
    conv => enter [1]; rw [l38 X1 X0]
  intro x y
  conv => enter [1]; rw [← l39 y x]

theorem Equation3_118_124_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h124 : Equation124 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h118 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h124 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_206_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h229 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation117_273_implies_Equation5 (G : Type*) [Magma G] (h117 : Equation117 G) (h273 : Equation273 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h117 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation53_209_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h209 : Equation209 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation117_271_implies_Equation63 (G : Type*) [Magma G] (h117 : Equation117 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h271 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l2 ((X1 ◇ X0) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ ((X0 ◇ X1) ◇ X1)) X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1]; rw [← h271 X0 X1]
    conv => enter [1, 2, 1]; rw [← h271 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 1]; rw [← h271 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [← h271 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation63_209_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h209 : Equation209 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h63 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l5 ((X1 ◇ (X1 ◇ X0)) ◇ X1) X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h63 X0 X1]
    conv => enter [1, 1, 2]; rw [← h63 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ (X1 ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l7 X1 X0]
    conv => enter [1, 1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [← h63 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← h63 X0 X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation117_261_implies_Equation63 (G : Type*) [Magma G] (h117 : Equation117 G) (h261 : Equation261 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h261 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation65_209_implies_Equation63 (G : Type*) [Magma G] (h65 : Equation65 G) (h209 : Equation209 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h65 (X0 ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 1, 1]; rw [l1 y x]
  conv => enter [1]; rw [l1 ((x ◇ y) ◇ x) y]
  conv => enter [1, 2]; rw [l1 (x ◇ y) x]

theorem Equation117_260_implies_Equation28 (G : Type*) [Magma G] (h117 : Equation117 G) (h260 : Equation260 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h260 X1 ((X0 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation49_209_implies_Equation9 (G : Type*) [Magma G] (h49 : Equation49 G) (h209 : Equation209 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_117_221_270_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h221 : Equation221 G) (h270 : Equation270 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_48_105_209_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h105 : Equation105 G) (h209 : Equation209 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation117_208_implies_Equation28 (G : Type*) [Magma G] (h117 : Equation117 G) (h208 : Equation208 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation101_209_implies_Equation9 (G : Type*) [Magma G] (h101 : Equation101 G) (h209 : Equation209 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation117_205_implies_Equation5 (G : Type*) [Magma G] (h117 : Equation117 G) (h205 : Equation205 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation104_209_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h209 : Equation209 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation117_159_209_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h159 : Equation159 G) (h209 : Equation209 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h209 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [l4 (X0 ◇ X1) X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l6 X0 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation117_118_222_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h118 : Equation118 G) (h222 : Equation222 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h222 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_209_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h229 X0 X1]
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h209 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation105_273_326_implies_Equation14 (G : Type*) [Magma G] (h105 : Equation105 G) (h273 : Equation273 G) (h326 : Equation326 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation105_273_326_implies_Equation66 (G : Type*) [Magma G] (h105 : Equation105 G) (h273 : Equation273 G) (h326 : Equation326 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_105_273_326_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h273 : Equation273 G) (h326 : Equation326 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation53_221_375_implies_Equation14 (G : Type*) [Magma G] (h53 : Equation53 G) (h221 : Equation221 G) (h375 : Equation375 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation53_221_326_375_implies_Equation66 (G : Type*) [Magma G] (h53 : Equation53 G) (h221 : Equation221 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_53_221_375_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h221 : Equation221 G) (h375 : Equation375 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

end Order3
