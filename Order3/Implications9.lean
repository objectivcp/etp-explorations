import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation53_377_implies_Equation9 (G : Type*) [Magma G] (h53 : Equation53 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h377 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h53 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation3_273_325_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h273 : Equation273 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h325 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_53_385_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h385 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation273_323_implies_Equation5 (G : Type*) [Magma G] (h273 : Equation273 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h323 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h273 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h273 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation53_378_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h378 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h53 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation271_385_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h385 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h385 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h271 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l14 X1 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation63_325_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h325 (X0 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h325 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1]; rw [← l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← l9 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l12 X1 X0]
    conv => enter [1]; rw [← h63 X0 X1]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation271_384_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
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

theorem Equation63_335_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h63 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
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

theorem Equation3_271_378_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h271 : Equation271 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h378 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h378 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_63_323_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h63 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h323 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation271_377_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation63_333_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation271_333_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h333 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h271 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation63_377_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h377 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h63 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation271_325_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h325 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h271 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation63_385_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h63 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h385 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h63 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation271_323_implies_Equation2 (G : Type*) [Magma G] (h271 : Equation271 G) (h323 : Equation323 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h323 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h271 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation63_378_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h378 : Equation378 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h378 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h63 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation270_384_implies_Equation2 (G : Type*) [Magma G] (h270 : Equation270 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h270 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation48_335_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation270_378_implies_Equation5 (G : Type*) [Magma G] (h270 : Equation270 G) (h378 : Equation378 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation48_323_implies_Equation4 (G : Type*) [Magma G] (h48 : Equation48 G) (h323 : Equation323 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation270_377_implies_Equation2 (G : Type*) [Magma G] (h270 : Equation270 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h270 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation48_333_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h48 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation270_335_implies_Equation2 (G : Type*) [Magma G] (h270 : Equation270 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ X0)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1, 2]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l14 X1 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation48_384_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h384 (X0 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h384 (X0 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1, 1]; rw [l12 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3_270_325_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h270 : Equation270 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← h325 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_48_385_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h385 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation270_271_326_implies_Equation2 (G : Type*) [Magma G] (h270 : Equation270 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h326 (X0 ◇ (X1 ◇ X1)) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ (X1 ◇ X1)) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X1)) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X1)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation48_63_375_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h63 : Equation63 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h375 X1 ((X1 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 (X1 ◇ ((X1 ◇ X1) ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X1) ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ X1) X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation264_385_implies_Equation2 (G : Type*) [Magma G] (h264 : Equation264 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h264 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation75_325_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h75 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation264_384_implies_Equation14 (G : Type*) [Magma G] (h264 : Equation264 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_264_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h264 : Equation264 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_264_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h264 : Equation264 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 y (x ◇ x)]

theorem Equation75_335_implies_Equation14 (G : Type*) [Magma G] (h75 : Equation75 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation3_75_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_75_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 y (x ◇ x)]

theorem Equation264_378_implies_Equation4 (G : Type*) [Magma G] (h264 : Equation264 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1, 1]; rw [← h378 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation75_323_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1, 2]; rw [← h323 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation264_377_implies_Equation102 (G : Type*) [Magma G] (h264 : Equation264 G) (h377 : Equation377 G) : Equation102 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h377 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation75_333_implies_Equation228 (G : Type*) [Magma G] (h75 : Equation75 G) (h333 : Equation333 G) : Equation228 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h333 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation264_333_implies_Equation2 (G : Type*) [Magma G] (h264 : Equation264 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h333 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h264 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation75_377_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h377 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h75 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_264_273_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_264_273_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_264_273_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation3_53_75_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h75 : Equation75 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_53_75_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h75 : Equation75 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation264_270_implies_Equation2 (G : Type*) [Magma G] (h264 : Equation264 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h264 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation48_75_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h75 : Equation75 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h75 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation263_326_375_384_implies_Equation2 (G : Type*) [Magma G] (h263 : Equation263 G) (h326 : Equation326 G) (h375 : Equation375 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h263 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h326 (X0 ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h375 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation55_326_335_375_implies_Equation2 (G : Type*) [Magma G] (h55 : Equation55 G) (h326 : Equation326 G) (h335 : Equation335 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h375 X1 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h326 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_263_378_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h378 : Equation378 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation3_55_323_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h323 : Equation323 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation3_263_377_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h377 : Equation377 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h377 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 (x ◇ x) y]

theorem Equation3_263_377_implies_Equation261 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h377 : Equation377 G) : Equation261 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h377 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1, 1]; rw [h377 x y]

theorem Equation3_263_377_implies_Equation26 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h377 : Equation377 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h377 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_55_333_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h333 : Equation333 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h333 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation3_55_333_implies_Equation65 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h333 : Equation333 G) : Equation65 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h333 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2]; rw [h333 y x]

theorem Equation3_55_333_implies_Equation16 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h333 : Equation333 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h333 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_263_335_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [h335 (x ◇ y) y]

theorem Equation3_263_335_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [h335 (x ◇ y) y]
  conv => enter [1, 2]; rw [l3 y x]

theorem Equation3_263_335_implies_Equation167 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_263_335_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 (x ◇ x) y]

theorem Equation3_263_335_implies_Equation65 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation3_263_335_implies_Equation26 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h335 : Equation335 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_55_384_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [h384 y (y ◇ x)]
  conv => enter [1, 1]; rw [l3 y x]
  conv => enter [1]; rw [l3 y (x ◇ y)]

theorem Equation3_55_384_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [h384 y (y ◇ x)]
  conv => enter [1, 1]; rw [l3 y x]

theorem Equation3_55_384_implies_Equation167 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation167 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h384 X1 X0]
    conv => enter [1]; rw [l4 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_55_384_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation3_55_384_implies_Equation261 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation261 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h384 X1 X0]
    conv => enter [1]; rw [l4 (X0 ◇ X1) X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation3_55_384_implies_Equation16 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h384 : Equation384 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_263_333_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h333 : Equation333 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_55_377_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h377 : Equation377 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation263_271_implies_Equation2 (G : Type*) [Magma G] (h263 : Equation263 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h263 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation55_63_implies_Equation2 (G : Type*) [Magma G] (h55 : Equation55 G) (h63 : Equation63 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h55 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_263_270_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h263 : Equation263 G) (h270 : Equation270 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h270 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_48_55_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h55 : Equation55 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h48 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation261_385_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation65_325_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation261_384_implies_Equation222 (G : Type*) [Magma G] (h261 : Equation261 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h384 (X0 ◇ X1) (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2]; rw [h384 y x]
  conv => enter [1]; rw [← l0 y (x ◇ y)]

theorem Equation261_384_implies_Equation167 (G : Type*) [Magma G] (h261 : Equation261 G) (h384 : Equation384 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation65_335_implies_Equation125 (G : Type*) [Magma G] (h65 : Equation65 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 x y]
  conv => enter [1, 1]; rw [h335 x y]
  conv => enter [1]; rw [← l0 y (y ◇ x)]

theorem Equation65_335_implies_Equation167 (G : Type*) [Magma G] (h65 : Equation65 G) (h335 : Equation335 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h335 (X0 ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation261_378_implies_Equation4 (G : Type*) [Magma G] (h261 : Equation261 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h378 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation65_323_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h323 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_261_377_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h261 : Equation261 G) (h377 : Equation377 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 (x ◇ x) y]

theorem Equation3_65_333_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h333 : Equation333 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 y (x ◇ x)]

theorem Equation261_335_implies_Equation209 (G : Type*) [Magma G] (h261 : Equation261 G) (h335 : Equation335 G) : Equation209 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h335 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h335 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2, 2, 2]; rw [← h335 y x]
  conv => enter [1]; rw [← h335 (x ◇ (y ◇ x)) y]

theorem Equation65_384_implies_Equation117 (G : Type*) [Magma G] (h65 : Equation65 G) (h384 : Equation384 G) : Equation117 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← h384 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 1, 1, 1]; rw [← h384 x y]
  conv => enter [1]; rw [← h384 y ((x ◇ y) ◇ x)]

theorem Equation261_326_333_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h326 : Equation326 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h333 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [l4 X1 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation65_375_377_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h375 : Equation375 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h377 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h377 X1 X0]
    conv => enter [1]; rw [l4 (X1 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation261_271_implies_Equation63 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l15 y x]

theorem Equation261_271_implies_Equation124 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1, 2]; rw [l14 x (y ◇ x)]

theorem Equation261_271_implies_Equation206 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l15 y x]
  conv => enter [1]; rw [l14 y (x ◇ (x ◇ y))]

theorem Equation261_271_implies_Equation65 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation261_271_implies_Equation117 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation117 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l15 y x]
  conv => enter [1, 2]; rw [l14 x (x ◇ y)]

theorem Equation261_271_implies_Equation209 (G : Type*) [Magma G] (h261 : Equation261 G) (h271 : Equation271 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1, 2, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ X0)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1]; rw [l14 y (x ◇ (y ◇ x))]

theorem Equation63_65_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h65 : Equation65 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 (((X1 ◇ X0) ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, ((((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 1]; rw [← l5 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l8 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l5 X0 (X0 ◇ X1)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l14 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [← l15 y x]

theorem Equation63_65_implies_Equation124 (G : Type*) [Magma G] (h63 : Equation63 G) (h65 : Equation65 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 (((X1 ◇ X0) ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, ((((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 1]; rw [← l5 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l8 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l5 X0 (X0 ◇ X1)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l14 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [← l15 y x]
  conv => enter [1]; rw [l14 ((y ◇ x) ◇ x) y]

theorem Equation63_65_implies_Equation206 (G : Type*) [Magma G] (h63 : Equation63 G) (h65 : Equation65 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 (((X1 ◇ X0) ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, ((((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 1]; rw [← l5 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l8 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l5 X0 (X0 ◇ X1)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [← l11 x y]
  conv => enter [1, 1]; rw [l14 (x ◇ y) x]

theorem Equation63_65_implies_Equation261 (G : Type*) [Magma G] (h63 : Equation63 G) (h65 : Equation65 G) : Equation261 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X1 X0 : G, ((((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 (((X1 ◇ X0) ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X1 X0 : G, ((((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 1]; rw [← l5 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation261_270_326_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h270 : Equation270 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h270 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation48_65_375_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h65 : Equation65 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h48 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ ((X0 ◇ X0) ◇ X1))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation260_385_implies_Equation28 (G : Type*) [Magma G] (h260 : Equation260 G) (h385 : Equation385 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation260_385_implies_Equation208 (G : Type*) [Magma G] (h260 : Equation260 G) (h385 : Equation385 G) : Equation208 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [h385 (y ◇ x) x]

theorem Equation49_325_implies_Equation9 (G : Type*) [Magma G] (h49 : Equation49 G) (h325 : Equation325 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation49_325_implies_Equation101 (G : Type*) [Magma G] (h49 : Equation49 G) (h325 : Equation325 G) : Equation101 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h325 x (x ◇ y)]

theorem Equation260_384_implies_Equation2 (G : Type*) [Magma G] (h260 : Equation260 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1, 1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation49_335_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1, 2]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_260_378_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h260 : Equation260 G) (h378 : Equation378 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h378 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation260_378_implies_Equation263 (G : Type*) [Magma G] (h260 : Equation260 G) (h378 : Equation378 G) : Equation263 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h378 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1]; rw [h378 x y]

theorem Equation3_49_323_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h323 : Equation323 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation49_323_implies_Equation55 (G : Type*) [Magma G] (h49 : Equation49 G) (h323 : Equation323 G) : Equation55 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2]; rw [h323 y x]

theorem Equation260_377_implies_Equation4 (G : Type*) [Magma G] (h260 : Equation260 G) (h377 : Equation377 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation49_333_implies_Equation5 (G : Type*) [Magma G] (h49 : Equation49 G) (h333 : Equation333 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h49 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation260_335_implies_Equation2 (G : Type*) [Magma G] (h260 : Equation260 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h335 X0 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1, 2]; rw [← l2 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← h335 (X1 ◇ X0) X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h335 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [l10 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l13 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l13 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l16 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation49_384_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h384 (X0 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h384 X0 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [l16 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l16 X1 X0]
    conv => enter [1]; rw [← l17 X1 X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X1 X0]
    conv => enter [1]; rw [l16 X1 X0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation260_333_implies_Equation270 (G : Type*) [Magma G] (h260 : Equation260 G) (h333 : Equation333 G) : Equation270 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation49_377_implies_Equation48 (G : Type*) [Magma G] (h49 : Equation49 G) (h377 : Equation377 G) : Equation48 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h49 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_260_271_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h260 : Equation260 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h326 (X0 ◇ (X1 ◇ X1)) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 ((X0 ◇ (X1 ◇ X1)) ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 (X0 ◇ (X1 ◇ X1)) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X1)]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_49_63_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h63 : Equation63 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h375 X1 ((X1 ◇ X1) ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X0 (X1 ◇ ((X1 ◇ X1) ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X1 ((X1 ◇ X1) ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l3 (X1 ◇ X1) X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_258_implies_Equation26 (G : Type*) [Magma G] (h3 : Equation3 G) (h258 : Equation258 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h258 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_258_implies_Equation362 (G : Type*) [Magma G] (h3 : Equation3 G) (h258 : Equation258 G) : Equation362 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h258 X0 X1]
  intro x y
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_72_implies_Equation16 (G : Type*) [Magma G] (h3 : Equation3 G) (h72 : Equation72 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h3 X0]
    conv => enter [1]; rw [← h72 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_72_implies_Equation315 (G : Type*) [Magma G] (h3 : Equation3 G) (h72 : Equation72 G) : Equation315 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h3 X0]
    conv => enter [1]; rw [← h72 X0 X1]
  intro x y
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_228_384_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1, 2]; rw [h384 y x]

theorem Equation3_228_384_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [h384 y x]
  conv => enter [1]; rw [l2 y (x ◇ y)]

theorem Equation3_228_384_implies_Equation167 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h384 : Equation384 G) : Equation167 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [l4 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_228_384_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h384 : Equation384 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation3_102_335_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h102 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [h335 (x ◇ y) y]

theorem Equation3_102_335_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h102 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [h335 x y]
  conv => enter [1]; rw [l2 y (y ◇ x)]

theorem Equation3_102_335_implies_Equation167 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h335 : Equation335 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h102 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_102_335_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h335 : Equation335 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h102 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h335 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 (x ◇ x) y]

theorem Equation228_375_378_implies_Equation5 (G : Type*) [Magma G] (h228 : Equation228 G) (h375 : Equation375 G) (h378 : Equation378 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h228 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h378 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation102_323_326_implies_Equation4 (G : Type*) [Magma G] (h102 : Equation102 G) (h323 : Equation323 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h102 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation228_375_377_implies_Equation2 (G : Type*) [Magma G] (h228 : Equation228 G) (h375 : Equation375 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h377 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h228 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation102_326_333_implies_Equation2 (G : Type*) [Magma G] (h102 : Equation102 G) (h326 : Equation326 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h333 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h102 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h102 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h102 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation228_335_implies_Equation2 (G : Type*) [Magma G] (h228 : Equation228 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation102_384_implies_Equation2 (G : Type*) [Magma G] (h102 : Equation102 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_228_325_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h325 : Equation325 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ X0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l0 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 1]; rw [l5 (X0 ◇ X1) X1]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 1]; rw [← l0 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 ((X1 ◇ X0) ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← l12 X1 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 ((X1 ◇ X0) ◇ X0) X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l14 X1 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3_102_326_385_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h326 : Equation326 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h385 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l0 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 (X1 ◇ X0)]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 (X1 ◇ (X1 ◇ X0)) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X0 ◇ X1))]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation228_323_implies_Equation28 (G : Type*) [Magma G] (h228 : Equation228 G) (h323 : Equation323 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h323 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation102_378_implies_Equation9 (G : Type*) [Magma G] (h102 : Equation102 G) (h378 : Equation378 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_228_271_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h271 : Equation271 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation3_63_102_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h102 : Equation102 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h63 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 (x ◇ x) y]

theorem Equation3_228_264_implies_Equation271 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h264 : Equation264 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_75_102_implies_Equation63 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h102 : Equation102 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h75 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_228_261_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h261 : Equation261 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [l4 y x]

theorem Equation3_228_261_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h261 : Equation261 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [l4 y x]
  conv => enter [1]; rw [← l5 y (x ◇ y)]

theorem Equation3_228_261_implies_Equation384 (G : Type*) [Magma G] (h3 : Equation3 G) (h228 : Equation228 G) (h261 : Equation261 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_65_102_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h102 : Equation102 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l4 (x ◇ y) y]

theorem Equation3_65_102_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h102 : Equation102 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [l4 x y]
  conv => enter [1]; rw [← l5 y (y ◇ x)]

theorem Equation3_65_102_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h102 : Equation102 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

end Order3
