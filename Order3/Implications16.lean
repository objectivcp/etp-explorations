import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation23_307_implies_Equation203 (G : Type*) [Magma G] (h23 : Equation23 G) (h307 : Equation307 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation47_307_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h307 X0]
    conv => enter [1]; rw [← h47 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation255_359_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h359 X0]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation151_359_implies_Equation8 (G : Type*) [Magma G] (h151 : Equation151 G) (h359 : Equation359 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h359 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_307_implies_Equation23 (G : Type*) [Magma G] (h151 : Equation151 G) (h307 : Equation307 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h307 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation203_255_307_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h255 : Equation255 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation47_99_359_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h99 : Equation99 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation203_307_359_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h307 : Equation307 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation99_307_359_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h307 : Equation307 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation99_203_307_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h203 : Equation203 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_203_359_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h203 : Equation203 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_359_implies_Equation8 (G : Type*) [Magma G] (h99 : Equation99 G) (h359 : Equation359 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_307_implies_Equation23 (G : Type*) [Magma G] (h203 : Equation203 G) (h307 : Equation307 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation364_365_implies_Equation372 (G : Type*) [Magma G] (h364 : Equation364 G) (h365 : Equation365 G) : Equation372 G := by
  have l0 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h364 sK2 sK1]
    conv => enter [1]; rw [h364 sK2 sK2]
    conv => enter [1, 1]; rw [h364 sK2 sK1]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h365 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h364 sK0 sK0]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h365 sK2 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 1]; rw [← l0 sK1 sK2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h364 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h364 sK2 sK1]
    conv => enter [1]; rw [l2 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h364 sK2 sK1]
    conv => enter [1]; rw [h365 sK2 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h364 sK2 sK1]
    conv => enter [1]; rw [h365 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1, 1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h365 sK1 (sK1 ◇ sK2)]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l1 sK0]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (((sK1 ◇ sK2) ◇ sK2) ◇ X0) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 1]; rw [← l4 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h365 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l11 sK1 sK2 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation308_313_implies_Equation317 (G : Type*) [Magma G] (h308 : Equation308 G) (h313 : Equation313 G) : Equation317 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h308 sK1 sK2]
    conv => enter [1]; rw [h308 sK1 sK1]
    conv => enter [1, 2]; rw [h308 sK1 sK2]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h308 sK0 sK0]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h313 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l0 sK1 sK2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h308 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h308 sK1 sK2]
    conv => enter [1]; rw [h313 sK1 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h308 sK1 sK2]
    conv => enter [1]; rw [h313 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h313 sK2 (sK1 ◇ sK2)]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [h308 sK2 sK2]
    conv => enter [1, 2]; rw [← l8 sK1 sK2]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [l10 sK2 sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 X0 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) X0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l1 sK0]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h313 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 sK0]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK0 sK2]
    conv => enter [1]; rw [← l16 sK2 sK0 sK0]
  have l18 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [l11 sK2 sK1 sK2]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK2 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation362_385_implies_Equation372 (G : Type*) [Magma G] (h362 : Equation362 G) (h385 : Equation385 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h362 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [← h362 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h362 sK1 sK2]
    conv => enter [1]; rw [h362 sK1 sK1]
    conv => enter [1, 1]; rw [h362 sK1 sK2]
  have l4 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← h362 ((sK1 ◇ sK2) ◇ sK2) sK1]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK2]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h362 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h362 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h385 X1 X1]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation315_325_implies_Equation317 (G : Type*) [Magma G] (h315 : Equation315 G) (h325 : Equation325 G) : Equation317 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h315 sK2 sK1]
    conv => enter [1]; rw [h315 sK2 sK2]
    conv => enter [1, 2]; rw [h315 sK2 sK1]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h315 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h315 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h325 X1 X1]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation362_367_implies_Equation372 (G : Type*) [Magma G] (h362 : Equation362 G) (h367 : Equation367 G) : Equation372 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [← h362 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h362 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h362 sK1 sK2]
    conv => enter [1]; rw [h362 sK1 sK1]
    conv => enter [1, 1]; rw [h362 sK1 sK2]
  have l4 : ∀ sK1 sK2 : G, (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← h362 ((sK1 ◇ sK2) ◇ sK2) sK1]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h362 (X1 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h367 X1 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [h362 X1 X1]
    conv => enter [1, 1]; rw [l9 X1 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l9 X0 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l13 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l12 sK1 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 X1]
    conv => enter [1, 1]; rw [l12 sK1 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1]; rw [← l13 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation310_315_implies_Equation317 (G : Type*) [Magma G] (h310 : Equation310 G) (h315 : Equation315 G) : Equation317 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h315 X0 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 X0]
    conv => enter [1]; rw [l1 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 sK2 sK1]
    conv => enter [1]; rw [h310 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [← l5 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation360_385_implies_Equation368 (G : Type*) [Magma G] (h360 : Equation360 G) (h385 : Equation385 G) : Equation368 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h360 sK1 X0]
    conv => enter [1]; rw [← h385 X0 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h360 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h360 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h360 y y]

theorem Equation312_325_implies_Equation316 (G : Type*) [Magma G] (h312 : Equation312 G) (h325 : Equation325 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h312 sK1 X0]
    conv => enter [1]; rw [← h325 (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h312 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation360_365_implies_Equation371 (G : Type*) [Magma G] (h360 : Equation360 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h365 X0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h360 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h360 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h365 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation312_313_implies_Equation319 (G : Type*) [Magma G] (h312 : Equation312 G) (h313 : Equation313 G) : Equation319 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h312 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h312 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h313 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation307_367_384_implies_Equation316 (G : Type*) [Magma G] (h307 : Equation307 G) (h367 : Equation367 G) (h384 : Equation384 G) : Equation316 G := by
  have l0 : ∀ X1 X0 sK0 : G, ((X1 ◇ X1) ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h367 X0 X1]
    conv => enter [1]; rw [h367 X0 sK0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h384 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h307 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X1)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h384 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h367 sK0 sK0]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X0) sK0]
  have l7 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l8 X0 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]
  conv => enter [1]; rw [h307 y]

theorem Equation307_367_384_implies_Equation368 (G : Type*) [Magma G] (h307 : Equation307 G) (h367 : Equation367 G) (h384 : Equation384 G) : Equation368 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h384 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  have l1 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h384 (sK1 ◇ sK1) sK1]
    conv => enter [1, 1]; rw [← h307 sK1]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h367 X0 sK1]
    conv => enter [1]; rw [← h384 X0 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l2 X0 sK1]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h367 (sK1 ◇ sK1) sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h367 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation310_335_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h335 : Equation335 G) : Equation316 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK1) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h335 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 X0 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← h310 (sK1 ◇ sK1) X0]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h310 (sK1 ◇ sK1) sK0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l6 X0 sK1 sK0]
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) sK0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l7 X0 sK1 sK0]
    conv => enter [1]; rw [← h310 (sK0 ◇ sK0) sK1]
  have l9 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l8 X0 sK1 X0]
    conv => enter [1]; rw [← l8 X1 sK1 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h310 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 X0]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← l10 sK1 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation310_335_implies_Equation368 (G : Type*) [Magma G] (h310 : Equation310 G) (h335 : Equation335 G) : Equation368 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK1]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l0 X0 sK0 sK1]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK1) X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h310 sK1 sK1]
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h335 X0 X0]
    conv => enter [1]; rw [l3 X0 sK1]
  have l6 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h335 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l6 sK1 ((sK1 ◇ sK1) ◇ sK1) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h335 ((sK1 ◇ sK1) ◇ sK1) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l7 ((sK1 ◇ sK1) ◇ sK1) sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← h310 (sK0 ◇ sK0) sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h335 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 X0 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l13 X0 sK1]
    conv => enter [1]; rw [← h310 (sK1 ◇ sK1) X0]
  have l15 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l14 X0 sK1]
    conv => enter [1]; rw [h310 (sK1 ◇ sK1) sK0]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l15 X0 sK1 sK0]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) sK0]
  have l17 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l16 X0 sK1 sK0]
    conv => enter [1]; rw [← h310 (sK0 ◇ sK0) sK1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 sK1]
    conv => enter [1]; rw [← l17 X0 sK1 sK1]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← l18 sK1 X0]
  intro x y
  conv => enter [1]; rw [l19 x y]
  conv => enter [1]; rw [l5 y y]

theorem Equation335_367_implies_Equation316 (G : Type*) [Magma G] (h335 : Equation335 G) (h367 : Equation367 G) : Equation316 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h335 sK0 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h335 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h335 sK1 sK1]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK1) sK1]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h335 sK1 sK1]
    conv => enter [1]; rw [l2 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h335 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h335 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h335 sK1 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h367 X0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l5 sK0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h367 X0 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← l7 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l8 (sK1 ◇ sK1) sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1]; rw [h335 y y]

theorem Equation310_384_implies_Equation316 (G : Type*) [Magma G] (h310 : Equation310 G) (h384 : Equation384 G) : Equation316 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK1]
  have l2 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ X1) X0]
  have l4 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h384 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h384 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 (X0 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l6 : ∀ X0 sK0 sK1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 1]; rw [l1 X0 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 X0 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h384 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l8 : ∀ X0 sK0 X1 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) sK0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h384 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [h310 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l11 : ∀ X1 X0 sK0 : G, ((X1 ◇ X1) ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l8 X0 sK0 X1]
    conv => enter [1]; rw [l4 X0 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h384 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ sK0) sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l11 X0 X0 sK0]
  have l15 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l14 X0 sK0]
  have l16 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h384 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l15 (X0 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l16 sK1 X0 sK0]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 sK1 X0]
  have l19 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 X0]
    conv => enter [1]; rw [l9 sK1 X0 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h384 sK0 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation310_384_implies_Equation368 (G : Type*) [Magma G] (h310 : Equation310 G) (h384 : Equation384 G) : Equation368 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l2 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h384 (X1 ◇ X1) X0]
  have l4 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h384 (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 sK0 X1 : G, ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X0) sK0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 sK0 : G, ((X1 ◇ X1) ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l5 X0 sK0 X1]
    conv => enter [1]; rw [l4 X0 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h384 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 sK0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l7 X0 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l7 X0 sK0]
  have l10 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h384 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l8 (X0 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← l10 sK1 X0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h384 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l9 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h384 sK1 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK1]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l15 X0 X0]
    conv => enter [1]; rw [← l14 sK1 X0]
  intro x y
  conv => enter [1]; rw [l16 x y]
  conv => enter [1]; rw [h384 y y]

theorem Equation310_323_364_implies_Equation372 (G : Type*) [Magma G] (h310 : Equation310 G) (h323 : Equation323 G) (h364 : Equation364 G) : Equation372 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h364 sK0 sK0]
    conv => enter [1]; rw [h323 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h364 sK0 sK0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h364 sK2 sK1]
    conv => enter [1]; rw [h364 sK2 sK2]
    conv => enter [1, 1]; rw [h364 sK2 sK1]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h323 ((sK1 ◇ sK2) ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [h310 ((sK1 ◇ sK2) ◇ sK2) sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK2) ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h364 (sK0 ◇ sK0) ((sK1 ◇ sK2) ◇ sK2)]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation308_367_378_implies_Equation317 (G : Type*) [Magma G] (h308 : Equation308 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation317 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h308 sK1 sK2]
    conv => enter [1]; rw [h308 sK1 sK1]
    conv => enter [1, 2]; rw [h308 sK1 sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h367 X0 sK1]
    conv => enter [1, 1]; rw [h308 sK1 sK2]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h367 X0 sK0]
    conv => enter [1]; rw [← h308 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h367 X0 sK0]
    conv => enter [1]; rw [l1 X0 sK1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 X0 sK1 sK2]
    conv => enter [1]; rw [← h308 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h367 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X0) sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK1 sK2]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h308 sK0 sK0]
    conv => enter [1]; rw [h378 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h308 sK0 sK0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [h378 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 1]; rw [← l0 sK1 sK2]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h367 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation274_307_implies_Equation3 (G : Type*) [Magma G] (h274 : Equation274 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1, 1]; rw [← h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation73_359_implies_Equation3 (G : Type*) [Magma G] (h73 : Equation73 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h73 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h73 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation274_283_implies_Equation231 (G : Type*) [Magma G] (h274 : Equation274 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h274 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← h283 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h283 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation274_283_implies_Equation151 (G : Type*) [Magma G] (h274 : Equation274 G) (h283 : Equation283 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h274 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h283 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation56_73_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h73 : Equation73 G) : Equation108 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h56 (sK1 ◇ sK1) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l0 sK1]
    conv => enter [1]; rw [← h56 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation56_73_implies_Equation151 (G : Type*) [Magma G] (h56 : Equation56 G) (h73 : Equation73 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h56 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation274_280_implies_Equation211 (G : Type*) [Magma G] (h274 : Equation274 G) (h280 : Equation280 G) : Equation211 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h274 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h274 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h280 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation274_280_implies_Equation40 (G : Type*) [Magma G] (h274 : Equation274 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, ((X0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 1, 1]; rw [h280 X0 sK0]
    conv => enter [1]; rw [← h274 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← h280 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h274 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h280 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation50_73_implies_Equation107 (G : Type*) [Magma G] (h50 : Equation50 G) (h73 : Equation73 G) : Equation107 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h73 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h50 (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation50_73_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h73 : Equation73 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [h50 X0 sK0]
    conv => enter [1]; rw [← h73 X0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← h50 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h73 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h50 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation263_309_310_323_implies_Equation266 (G : Type*) [Magma G] (h263 : Equation263 G) (h309 : Equation309 G) (h310 : Equation310 G) (h323 : Equation323 G) : Equation266 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← h323 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h263 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK2)]
    conv => enter [1, 1, 1]; rw [← h323 (sK0 ◇ sK1) sK2]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 1, 1]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h310 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h263 (((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) (sK0 ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l3 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← h310 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK2)]
  have l8 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h310 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h310 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h310 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = ((((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l8 (sK0 ◇ X0) (sK0 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l13 sK0 X0 sK1]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((((sK0 ◇ sK1) ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 X0 sK1 sK0]
    conv => enter [1, 1]; rw [← l12 sK0 sK1 sK2 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 ((sK0 ◇ sK1) ◇ sK2) sK0]
    conv => enter [1, 1]; rw [← l15 sK0 ((sK0 ◇ sK1) ◇ sK2) sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, sK0 = (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h263 sK0 ((sK0 ◇ sK1) ◇ sK2)]
    conv => enter [1, 1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation55_361_367_378_implies_Equation58 (G : Type*) [Magma G] (h55 : Equation55 G) (h361 : Equation361 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation58 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h55 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h378 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X0 ◇ X1)]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h55 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h378 sK1 (sK2 ◇ sK0)]
  have l3 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h55 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h378 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h55 ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← h367 ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
  have l6 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h55 ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK2]
  have l7 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0]
    conv => enter [1]; rw [← h367 (sK0 ◇ sK0) (sK2 ◇ sK0)]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h367 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l1 X2 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l9 X1 X0]
  have l11 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((X0 ◇ X0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h367 ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) X0]
  have l12 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((X0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ sK0) = ((X0 ◇ sK0) ◇ ((X1 ◇ X1) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [← l8 (X0 ◇ sK0) X1 (X0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l12 X0 sK0 sK2]
  have l14 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = ((X0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X0 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 sK0 X0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l14 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h55 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation261_274_implies_Equation3 (G : Type*) [Magma G] (h261 : Equation261 G) (h274 : Equation274 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h261 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 1, 1]; rw [← h261 sK0 sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h261 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h261 sK0 sK0]
    conv => enter [1, 1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation65_73_implies_Equation3 (G : Type*) [Magma G] (h65 : Equation65 G) (h73 : Equation73 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h65 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← h65 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h73 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h65 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h65 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation47_274_implies_Equation99 (G : Type*) [Magma G] (h47 : Equation47 G) (h274 : Equation274 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1, 1]; rw [h47 sK0]
    conv => enter [1]; rw [← h274 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation47_274_implies_Equation203 (G : Type*) [Magma G] (h47 : Equation47 G) (h274 : Equation274 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 1]; rw [← h47 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 sK0 sK0]
    conv => enter [1, 1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation73_255_implies_Equation99 (G : Type*) [Magma G] (h73 : Equation73 G) (h255 : Equation255 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h255 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation73_255_implies_Equation203 (G : Type*) [Magma G] (h73 : Equation73 G) (h255 : Equation255 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [h255 sK0]
    conv => enter [1]; rw [← h73 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h255 sK0]
    conv => enter [1, 1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation47_229_283_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h283 : Equation283 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h229 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1, 2]; rw [← h47 sK1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h283 X0 sK1]
  have l2 : ∀ sK1 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [← h229 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [l2 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation229_283_implies_Equation108 (G : Type*) [Magma G] (h229 : Equation229 G) (h283 : Equation283 G) : Equation108 G := by
  have l0 : ∀ sK1 X0 : G, ((((sK1 ◇ sK1) ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [h283 X0 sK1]
    conv => enter [1]; rw [← h229 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h283 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation47_229_283_implies_Equation231 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h229 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1, 2]; rw [← h47 sK1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h283 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation47_229_283_implies_Equation151 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h283 : Equation283 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h229 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 2]; rw [← h47 sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h229 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← h47 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h229 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← l0 sK0]
  have l3 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h283 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h283 X0 sK0]
  have l5 : ∀ sK0 X0 : G, ((((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = X0 := by
    intro sK0 X0
    conv => enter [1, 1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [← h229 X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = X0 := by
    intro X0 sK0
    conv => enter [1, 1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l4 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h229 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

theorem Equation56_118_implies_Equation283 (G : Type*) [Magma G] (h56 : Equation56 G) (h118 : Equation118 G) : Equation283 G := by
  have l0 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h118 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← h118 sK1 sK1]
  have l1 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1, 2]; rw [← h118 sK1 sK1]
  have l2 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h118 ((sK1 ◇ sK1) ◇ sK1) sK1]
    conv => enter [1, 2, 1]; rw [← l1 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [← h56 X0 sK1]
  have l4 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [← l3 X0 sK1]
    conv => enter [1]; rw [← h118 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l3 X0 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation56_118_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h118 : Equation118 G) : Equation108 G := by
  have l0 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h118 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← h118 sK1 sK1]
  have l1 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1, 2]; rw [← h118 sK1 sK1]
  have l2 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h118 ((sK1 ◇ sK1) ◇ sK1) sK1]
    conv => enter [1, 2, 1]; rw [← l1 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [← h56 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation56_118_implies_Equation231 (G : Type*) [Magma G] (h56 : Equation56 G) (h118 : Equation118 G) : Equation231 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [h56 X0 sK1]
    conv => enter [1]; rw [← h118 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h56 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation56_118_implies_Equation151 (G : Type*) [Magma G] (h56 : Equation56 G) (h118 : Equation118 G) : Equation151 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = X0 := by
    intro sK0 X0
    conv => enter [1, 2, 1]; rw [h56 X0 sK0]
    conv => enter [1]; rw [← h118 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h56 X0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h118 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation47_229_280_implies_Equation50 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h280 : Equation280 G) : Equation50 G := by
  have l0 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h229 X0 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h280 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ sK1 X0 : G, ((((sK1 ◇ sK1) ◇ X0) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h229 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h280 X0 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1]; rw [l1 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l4 X0 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (((X0 ◇ X0) ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h229 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l5 sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 1]; rw [← l5 sK1 X0]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) sK1]
    conv => enter [1, 2]; rw [← l7 sK1 X0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1]; rw [← l5 sK1 X0]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation229_280_implies_Equation107 (G : Type*) [Magma G] (h229 : Equation229 G) (h280 : Equation280 G) : Equation107 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h229 sK0 ((sK1 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← h280 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 1]; rw [← h280 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation229_280_implies_Equation211 (G : Type*) [Magma G] (h229 : Equation229 G) (h280 : Equation280 G) : Equation211 G := by
  have l0 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h229 X0 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h280 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ sK1 X0 : G, ((((sK1 ◇ sK1) ◇ X0) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h229 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h280 X0 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1]; rw [l1 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l4 X0 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (((X0 ◇ X0) ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h229 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l5 sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 1]; rw [← l5 sK1 X0]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) sK1]
    conv => enter [1, 2]; rw [← l7 sK1 X0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1]; rw [← l5 sK1 X0]
  have l10 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h229 X0 X0]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation47_229_280_implies_Equation40 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h229 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h47 X0]
  have l1 : ∀ sK0 X0 : G, ((((sK0 ◇ sK0) ◇ X0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) = X0 := by
    intro sK0 X0
    conv => enter [1, 1, 2]; rw [h280 X0 sK0]
    conv => enter [1]; rw [← h229 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 1]; rw [h280 X0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK1 X0 : G, ((((sK1 ◇ sK1) ◇ X0) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h229 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h280 X0 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h280 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1]; rw [l2 (sK1 ◇ sK1) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h229 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 1]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h229 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation50_118_255_implies_Equation280 (G : Type*) [Magma G] (h50 : Equation50 G) (h118 : Equation118 G) (h255 : Equation255 G) : Equation280 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h118 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h118 X0 (X0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h50 X0 sK1]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h50 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [← l2 X0 sK1]
    conv => enter [1]; rw [← h118 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h118 (X0 ◇ (X1 ◇ X1)) X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (((sK1 ◇ sK1) ◇ (X0 ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h50 ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) sK1]
    conv => enter [1, 2]; rw [l3 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l7 sK1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 sK1]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h118 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l8 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1, 2]; rw [l10 (sK1 ◇ sK1) X0 sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l12 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x y
  conv => enter [1]; rw [← l14 y x]

theorem Equation50_118_255_implies_Equation107 (G : Type*) [Magma G] (h50 : Equation50 G) (h118 : Equation118 G) (h255 : Equation255 G) : Equation107 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h118 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h118 X0 (X0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h50 X0 sK1]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h50 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [← l2 X0 sK1]
    conv => enter [1]; rw [← h118 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h118 (X0 ◇ (X1 ◇ X1)) X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (((sK1 ◇ sK1) ◇ (X0 ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h50 ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) sK1]
    conv => enter [1, 2]; rw [l3 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l7 sK1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 sK1]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h118 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l8 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1, 2]; rw [l10 (sK1 ◇ sK1) X0 sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l9 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l12 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← h255 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h118 ((sK1 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 2, 1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h50 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation50_118_implies_Equation211 (G : Type*) [Magma G] (h50 : Equation50 G) (h118 : Equation118 G) : Equation211 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 1]; rw [← h50 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← h50 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation50_118_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h118 : Equation118 G) : Equation40 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h118 X0 (X0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h50 X0 sK1]
    conv => enter [1]; rw [l0 X0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h50 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h118 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h50 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation229_264_implies_Equation73 (G : Type*) [Magma G] (h229 : Equation229 G) (h264 : Equation264 G) : Equation73 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h264 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 1, 1]; rw [← h229 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h264 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation229_264_implies_Equation125 (G : Type*) [Magma G] (h229 : Equation229 G) (h264 : Equation264 G) : Equation125 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h264 (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) sK1]
    conv => enter [1, 1, 1]; rw [← h229 ((sK1 ◇ sK0) ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h264 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h229 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) sK1]
    conv => enter [1, 1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h229 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation75_118_implies_Equation222 (G : Type*) [Magma G] (h75 : Equation75 G) (h118 : Equation118 G) : Equation222 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h118 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← h75 (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h118 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) sK1]
    conv => enter [1, 2, 1]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation229_231_implies_Equation56 (G : Type*) [Magma G] (h229 : Equation229 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ sK1 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 2]; rw [h231 X0 sK1]
    conv => enter [1]; rw [← h229 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h231 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation47_229_231_implies_Equation283 (G : Type*) [Magma G] (h47 : Equation47 G) (h229 : Equation229 G) (h231 : Equation231 G) : Equation283 G := by
  have l0 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 1, 2]; rw [h47 sK1]
    conv => enter [1]; rw [← h229 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h231 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation108_118_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h118 : Equation118 G) : Equation56 G := by
  have l0 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [h108 X0 sK1]
    conv => enter [1]; rw [← h118 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h108 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [← h118 ((sK1 ◇ sK1) ◇ sK1) X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← h108 X0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l3 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation211_229_implies_Equation50 (G : Type*) [Magma G] (h211 : Equation211 G) (h229 : Equation229 G) : Equation50 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h229 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 1, 2]; rw [← h229 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h211 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation47_99_211_229_implies_Equation280 (G : Type*) [Magma G] (h47 : Equation47 G) (h99 : Equation99 G) (h211 : Equation211 G) (h229 : Equation229 G) : Equation280 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h229 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h47 X0]
  have l1 : ∀ X0 sK1 : G, (((X0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h211 X0 sK1]
    conv => enter [1]; rw [← h229 X0 (X0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h211 X0 sK1]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 1]; rw [← l2 X0 sK1]
    conv => enter [1]; rw [← h229 (sK1 ◇ sK1) X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h99 X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h229 ((sK1 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h211 sK0 sK1]
    conv => enter [1, 1]; rw [← l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation47_107_118_implies_Equation50 (G : Type*) [Magma G] (h47 : Equation47 G) (h107 : Equation107 G) (h118 : Equation118 G) : Equation50 G := by
  have l0 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [h107 X0 sK1]
    conv => enter [1]; rw [← h118 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h107 X0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [← h118 (sK1 ◇ sK1) X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation47_118_283_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h118 : Equation118 G) (h283 : Equation283 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h118 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← h118 sK1 sK1]
  have l1 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1, 2]; rw [← h118 sK1 sK1]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h118 ((sK1 ◇ sK1) ◇ sK1) sK1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h283 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l3 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [← l3 sK1 X0]
    conv => enter [1]; rw [← h118 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 1]; rw [l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation56_229_255_implies_Equation283 (G : Type*) [Magma G] (h56 : Equation56 G) (h229 : Equation229 G) (h255 : Equation255 G) : Equation283 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h56 X0 sK1]
    conv => enter [1]; rw [← h229 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ X0 : G, ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h229 X0 ((X0 ◇ X0) ◇ X0)]
  have l2 : ∀ sK1 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l0 X0 sK1]
    conv => enter [1, 1, 1]; rw [← l0 X0 sK1]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h56 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation47_118_280_implies_Equation50 (G : Type*) [Magma G] (h47 : Equation47 G) (h118 : Equation118 G) (h280 : Equation280 G) : Equation50 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h118 (sK1 ◇ sK1) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation50_229_implies_Equation280 (G : Type*) [Magma G] (h50 : Equation50 G) (h229 : Equation229 G) : Equation280 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h229 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h229 (sK1 ◇ sK1) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [← l0 X0 sK1]
    conv => enter [1, 1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [l1 sK1 X0]
    conv => enter [1]; rw [← h229 X0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation47_118_231_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h118 : Equation118 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h118 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h231 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [h231 X0 sK1]
    conv => enter [1]; rw [← h118 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l1 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation108_229_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h229 : Equation229 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h229 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← h108 (sK1 ◇ sK1) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h108 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation118_211_255_implies_Equation50 (G : Type*) [Magma G] (h118 : Equation118 G) (h211 : Equation211 G) (h255 : Equation255 G) : Equation50 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [h211 X0 sK1]
    conv => enter [1]; rw [← h118 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h118 ((X0 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l2 X0 sK1]
    conv => enter [1]; rw [← h118 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation47_107_229_implies_Equation50 (G : Type*) [Magma G] (h47 : Equation47 G) (h107 : Equation107 G) (h229 : Equation229 G) : Equation50 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h47 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h107 (sK1 ◇ sK1) sK1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h107 X0 X1]
    conv => enter [1]; rw [← h229 ((X1 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h107 X0 sK1]
    conv => enter [1]; rw [← h229 ((sK1 ◇ sK1) ◇ X0) X0]
  have l3 : ∀ X1 X0 sK1 : G, ((X1 ◇ X1) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 sK1]
  have l4 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (((sK1 ◇ sK1) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l3 sK1 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X0 (X0 ◇ X0) sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 X0 (X0 ◇ X0) sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [h107 (X0 ◇ X0) sK1]
    conv => enter [1]; rw [l3 X0 ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) sK1]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) sK1]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 sK1]
    conv => enter [1, 2]; rw [l3 X0 ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) sK1]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1, 2]; rw [← l6 X0 sK1]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = (((sK1 ◇ sK1) ◇ (X0 ◇ X0)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h229 (X0 ◇ X0) (sK1 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l9 X0 sK1]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l10 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ sK1) X0]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l11 X0 sK1]
    conv => enter [1]; rw [← l0 sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x y
  conv => enter [1]; rw [← l13 x y]

theorem Equation43_365_implies_Equation315 (G : Type*) [Magma G] (h43 : Equation43 G) (h365 : Equation365 G) : Equation315 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1, 1]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation43_365_implies_Equation362 (G : Type*) [Magma G] (h43 : Equation43 G) (h365 : Equation365 G) : Equation362 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1, 1]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation43_364_implies_Equation309 (G : Type*) [Magma G] (h43 : Equation43 G) (h364 : Equation364 G) : Equation309 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1, 1]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation43_364_implies_Equation361 (G : Type*) [Magma G] (h43 : Equation43 G) (h364 : Equation364 G) : Equation361 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1, 1]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation43_308_implies_Equation309 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) : Equation309 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h308 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_308_implies_Equation361 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) : Equation361 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h308 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation23_73_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h73 : Equation73 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h73 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h23 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h23 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h73 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1, 2]; rw [← h23 sK0]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [← l5 sK0]
  intro x
  conv => enter [1]; rw [l6 x]

theorem Equation8_274_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h274 : Equation274 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h274 (X0 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h8 X0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 sK0 sK0]
    conv => enter [1, 1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation50_63_implies_Equation31 (G : Type*) [Magma G] (h50 : Equation50 G) (h63 : Equation63 G) : Equation31 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h63 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation50_63_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h63 : Equation63 G) : Equation40 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h50 X0 sK0]
    conv => enter [1]; rw [← h63 X0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h50 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation271_280_implies_Equation11 (G : Type*) [Magma G] (h271 : Equation271 G) (h280 : Equation280 G) : Equation11 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h271 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation271_280_implies_Equation40 (G : Type*) [Magma G] (h271 : Equation271 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 1]; rw [h280 X0 sK0]
    conv => enter [1]; rw [← h271 X0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h280 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l0 (X0 ◇ X0) sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation31_63_implies_Equation50 (G : Type*) [Magma G] (h31 : Equation31 G) (h63 : Equation63 G) : Equation50 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h31 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation11_271_implies_Equation280 (G : Type*) [Magma G] (h11 : Equation11 G) (h271 : Equation271 G) : Equation280 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h11 (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation261_384_implies_Equation118 (G : Type*) [Magma G] (h261 : Equation261 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [h261 sK0 sK1]
    conv => enter [1]; rw [← h384 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h384 sK0 sK1]
    conv => enter [1, 1]; rw [h384 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 sK1 sK0]
    conv => enter [1, 1, 1]; rw [h384 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 1]; rw [← h384 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h384 sK0 ((sK0 ◇ sK1) ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, sK1 = (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 sK1 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l1 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, sK1 = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h384 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h384 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l0 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← h384 ((sK0 ◇ sK1) ◇ sK1) sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation3_261_384_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h261 : Equation261 G) (h384 : Equation384 G) : Equation72 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 sK1 sK0]
    conv => enter [1, 1, 1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h384 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ X0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h384 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h3 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h384 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) (sK0 ◇ sK1)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h384 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1, 1, 2, 2]; rw [h3 sK0]
  have l13 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2]; rw [← h384 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation65_335_implies_Equation73 (G : Type*) [Magma G] (h65 : Equation65 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← h65 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h335 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [h335 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h335 (sK0 ◇ sK1) sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h335 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_65_335_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h335 : Equation335 G) : Equation258 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 sK1 sK0]
    conv => enter [1, 2, 2, 1]; rw [h3 sK0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h335 (X0 ◇ (X1 ◇ X0)) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1, 2, 1]; rw [h3 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [← h3 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← h335 ((sK0 ◇ sK0) ◇ sK1) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [← h3 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h335 (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, sK1 = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 sK1 (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, sK1 = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, sK1 = (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l2 ((sK0 ◇ sK0) ◇ sK1) sK0]
  have l16 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ((sK0 ◇ sK0) ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((((sK0 ◇ sK0) ◇ sK1) ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ((sK0 ◇ sK0) ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 1]; rw [← h335 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation3_261_271_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h261 : Equation261 G) (h271 : Equation271 G) : Equation332 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 sK1 sK0]
    conv => enter [1, 1, 1, 2]; rw [h3 sK0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 sK1 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h261 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← h271 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l3 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 (sK1 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l4 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 ((sK0 ◇ sK1) ◇ sK0) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 1]; rw [← l3 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 1, 1]; rw [← l8 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 1]; rw [← l6 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 1, 1]; rw [← l9 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, sK1 = ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← l11 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1, 1]; rw [← h261 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 1]; rw [← l18 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2, 1]; rw [l16 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l24 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation3_63_65_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h65 : Equation65 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h63 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h3 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h65 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 (sK0 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 (sK1 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l13 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [← h65 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, sK1 = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 sK1 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, sK1 = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 ((sK0 ◇ sK1) ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l18 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 1, 2]; rw [← l16 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l24 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation3_206_271_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h271 : Equation271 G) : Equation332 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← h206 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 sK1]
    conv => enter [1, 1, 1, 2]; rw [h3 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← h271 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 sK1 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h206 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← l0 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h206 (sK1 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h206 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← l4 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h271 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 1]; rw [← l4 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 ((sK0 ◇ sK1) ◇ sK1) sK1]
    conv => enter [1, 1, 1]; rw [← l9 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 1]; rw [← l13 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h206 (sK1 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 1, 2]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation3_63_124_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h124 : Equation124 G) : Equation332 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h63 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h124 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 1]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h124 sK0 sK1]
    conv => enter [1, 2, 1, 2]; rw [h3 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h124 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h124 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l4 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h124 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h63 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h124 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 (sK1 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation205_261_implies_Equation9 (G : Type*) [Magma G] (h205 : Equation205 G) (h261 : Equation261 G) : Equation9 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 1, 1]; rw [← h205 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h205 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation65_104_implies_Equation28 (G : Type*) [Magma G] (h65 : Equation65 G) (h104 : Equation104 G) : Equation28 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 ((sK1 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h104 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h104 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_117_271_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h271 : Equation271 G) : Equation332 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← h271 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h117 (sK1 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h117 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 1]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 1, 1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 1]; rw [← h271 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h117 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h117 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h271 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1, 1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h117 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_63_209_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h209 : Equation209 G) : Equation332 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h63 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h209 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h209 (sK0 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 1]; rw [← l1 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, sK1 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [← h63 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h209 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h209 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 1]; rw [← l6 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h63 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h209 (sK0 ◇ sK1) sK0]
    conv => enter [1, 1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_117_261_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h261 : Equation261 G) : Equation332 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h117 sK1 sK0]
    conv => enter [1, 2, 1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h117 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h261 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_65_209_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h209 : Equation209 G) : Equation332 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h209 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← h209 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_105_263_375_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h263 : Equation263 G) (h375 : Equation375 G) : Equation258 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 sK0 sK1]
    conv => enter [1, 1, 1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) sK0]
    conv => enter [1, 1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h375 sK0 (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h105 (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) sK0]
    conv => enter [1, 2, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_55_221_326_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h221 : Equation221 G) (h326 : Equation326 G) : Equation72 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h55 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h3 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h55 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h326 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h221 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation65_260_implies_Equation28 (G : Type*) [Magma G] (h65 : Equation65 G) (h260 : Equation260 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X0 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation49_261_implies_Equation9 (G : Type*) [Magma G] (h49 : Equation49 G) (h261 : Equation261 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h49 X1 ((X0 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation211_274_implies_Equation280 (G : Type*) [Magma G] (h211 : Equation211 G) (h274 : Equation274 G) : Equation280 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h211 X0 sK1]
    conv => enter [1]; rw [← h274 (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h274 X0 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation73_107_implies_Equation50 (G : Type*) [Magma G] (h73 : Equation73 G) (h107 : Equation107 G) : Equation50 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h107 X0 sK1]
    conv => enter [1]; rw [← h73 (sK1 ◇ sK1) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h73 X0 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation159_274_implies_Equation3 (G : Type*) [Magma G] (h159 : Equation159 G) (h274 : Equation274 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h159 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← h274 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h274 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h274 sK0 sK0]
    conv => enter [1, 1]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation73_159_implies_Equation3 (G : Type*) [Magma G] (h73 : Equation73 G) (h159 : Equation159 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h159 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1]; rw [← h73 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [← h73 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h73 sK0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

theorem Equation99_151_231_274_implies_Equation56 (G : Type*) [Magma G] (h99 : Equation99 G) (h151 : Equation151 G) (h231 : Equation231 G) (h274 : Equation274 G) : Equation56 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 1]; rw [h231 X0 sK1]
    conv => enter [1]; rw [← h274 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X0)) sK1]
    conv => enter [1, 1]; rw [← h231 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [← h231 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l3 X0 sK1]
    conv => enter [1]; rw [← h99 X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation56_73_203_implies_Equation283 (G : Type*) [Magma G] (h56 : Equation56 G) (h73 : Equation73 G) (h203 : Equation203 G) : Equation283 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h56 (sK1 ◇ sK1) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l0 sK1]
    conv => enter [1]; rw [← h56 X0 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 sK1]
    conv => enter [1]; rw [← h73 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h56 ((sK1 ◇ sK1) ◇ sK1) X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [l1 ((sK1 ◇ sK1) ◇ sK1) sK1]
  have l5 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [← l4 X0 sK1]
    conv => enter [1]; rw [← h203 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation108_274_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h274 : Equation274 G) : Equation56 G := by
  have l0 : ∀ sK1 X0 : G, ((((sK1 ◇ sK1) ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h108 (((sK1 ◇ sK1) ◇ sK1) ◇ X0) sK1]
    conv => enter [1]; rw [← h274 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h108 (((sK1 ◇ sK1) ◇ sK1) ◇ X0) sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h274 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [l1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h108 X0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation108_274_implies_Equation283 (G : Type*) [Magma G] (h108 : Equation108 G) (h274 : Equation274 G) : Equation283 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h274 sK0 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1]; rw [← h108 (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h108 (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation73_231_implies_Equation56 (G : Type*) [Magma G] (h73 : Equation73 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h231 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h231 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation107_274_implies_Equation280 (G : Type*) [Magma G] (h107 : Equation107 G) (h274 : Equation274 G) : Equation280 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h274 ((sK1 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 1, 1]; rw [← h107 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h274 sK0 sK0]
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation73_211_implies_Equation50 (G : Type*) [Magma G] (h73 : Equation73 G) (h211 : Equation211 G) : Equation50 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [h211 X0 sK1]
    conv => enter [1]; rw [← h73 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l0 X0 sK1]
    conv => enter [1]; rw [← h73 X0 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation47_231_274_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h231 : Equation231 G) (h274 : Equation274 G) : Equation56 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 1]; rw [h231 X0 sK1]
    conv => enter [1]; rw [← h274 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X0)) sK1]
    conv => enter [1, 1]; rw [← h231 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [← h231 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1, 1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation47_231_274_implies_Equation283 (G : Type*) [Magma G] (h47 : Equation47 G) (h231 : Equation231 G) (h274 : Equation274 G) : Equation283 G := by
  have l0 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 1, 1]; rw [h47 sK1]
    conv => enter [1]; rw [← h274 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h231 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation73_108_255_implies_Equation56 (G : Type*) [Magma G] (h73 : Equation73 G) (h108 : Equation108 G) (h255 : Equation255 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2, 2]; rw [h255 sK1]
    conv => enter [1]; rw [← h73 ((sK1 ◇ sK1) ◇ sK1) sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [← h108 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation75_274_implies_Equation118 (G : Type*) [Magma G] (h75 : Equation75 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h75 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation73_264_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h264 : Equation264 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [← h264 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h264 X1 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← h73 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation75_118_127_222_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h118 : Equation118 G) (h127 : Equation127 G) (h222 : Equation222 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h118 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2, 2]; rw [h118 sK1 sK1]
    conv => enter [1]; rw [← h75 ((sK1 ◇ sK1) ◇ sK1) sK1]
  have l2 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h75 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK1]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h75 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h118 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1, 2]; rw [← l1 sK1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h75 ((X1 ◇ X1) ◇ X0) X1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [← h127 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [l4 sK1]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l5 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l5 X0 ((X0 ◇ X0) ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1, 2]; rw [← h127 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h127 X1 X0]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1, 1, 2]; rw [← l6 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l9 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← h127 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l13 sK1 X0]
    conv => enter [1, 2]; rw [← l12 sK1 X0]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h222 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1]; rw [l14 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [← l14 sK1 X0]
    conv => enter [1]; rw [← h118 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l16 sK1 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 1]; rw [l17 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation73_125_151_212_264_implies_Equation56 (G : Type*) [Magma G] (h73 : Equation73 G) (h125 : Equation125 G) (h151 : Equation151 G) (h212 : Equation212 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2, 1]; rw [h125 sK1 sK1]
    conv => enter [1]; rw [← h125 ((sK1 ◇ sK1) ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h73 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h151 sK1]
  have l2 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1, 2]; rw [← l0 sK1]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ sK1) ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h151 sK1]
    conv => enter [1]; rw [← h212 X0 (sK1 ◇ sK1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h212 X0 X1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h73 (X0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l3 X0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h264 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1, 1]; rw [← l2 sK1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h73 ((X0 ◇ X1) ◇ X1) X1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2, 1]; rw [l9 sK1]
    conv => enter [1]; rw [← h125 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l11 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l10 sK1]
  have l12 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [l11 sK1]
  have l13 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [l12 sK1]
    conv => enter [1]; rw [← h212 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l7 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l13 X0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h73 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation73_283_implies_Equation56 (G : Type*) [Magma G] (h73 : Equation73 G) (h283 : Equation283 G) : Equation56 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [h283 X0 sK1]
    conv => enter [1]; rw [← h73 ((sK1 ◇ sK1) ◇ sK1) X0]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h283 (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) sK1]
    conv => enter [1]; rw [← h73 X0 ((sK1 ◇ sK1) ◇ sK1)]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [h283 (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l2 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation56_274_implies_Equation283 (G : Type*) [Magma G] (h56 : Equation56 G) (h274 : Equation274 G) : Equation283 G := by
  have l0 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 1, 1]; rw [h56 X0 sK1]
    conv => enter [1]; rw [← h274 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ sK1 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h56 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) sK1]
    conv => enter [1]; rw [← h274 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [h56 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ sK1) ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation73_280_implies_Equation50 (G : Type*) [Magma G] (h73 : Equation73 G) (h280 : Equation280 G) : Equation50 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [h280 X0 sK1]
    conv => enter [1]; rw [← h73 ((sK1 ◇ sK1) ◇ X0) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l0 X0 sK1]
    conv => enter [1]; rw [← h73 X0 X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← l1 X0 sK1]
    conv => enter [1]; rw [← h73 (sK1 ◇ sK1) X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h73 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation50_99_203_274_implies_Equation280 (G : Type*) [Magma G] (h50 : Equation50 G) (h99 : Equation99 G) (h203 : Equation203 G) (h274 : Equation274 G) : Equation280 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h50 X0 X1]
  have l1 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 1, 1]; rw [h50 X0 sK1]
    conv => enter [1]; rw [← h274 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X0) = X0 := by
    intro X0 sK1
    conv => enter [1, 1]; rw [l2 X0 sK1 X0]
    conv => enter [1]; rw [← h203 X0]
  have l4 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (((X0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X0) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h274 (X1 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1 sK1]
  have l5 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l4 X1 X1 sK1]
    conv => enter [1]; rw [← h274 (sK1 ◇ sK1) X1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h99 X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h274 ((sK1 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 1, 1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1, 1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation274_384_implies_Equation118 (G : Type*) [Magma G] (h274 : Equation274 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h384 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h274 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1, 2]; rw [h384 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation229_335_implies_Equation73 (G : Type*) [Magma G] (h229 : Equation229 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [h335 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_49_205_260_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h205 : Equation205 G) (h260 : Equation260 G) : Equation52 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h205 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) sK0]
    conv => enter [1, 1, 2]; rw [← h260 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1]; rw [← h260 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_49_104_260_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h104 : Equation104 G) (h260 : Equation260 G) : Equation52 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h104 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h260 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_49_159_260_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h159 : Equation159 G) (h260 : Equation260 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h260 X0 (X1 ◇ X0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h3 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_28_65_228_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h28 : Equation28 G) (h65 : Equation65 G) (h228 : Equation228 G) : Equation72 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h28 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h228 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_9_102_261_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h9 : Equation9 G) (h102 : Equation102 G) (h261 : Equation261 G) : Equation258 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 sK0 sK1]
    conv => enter [1, 1, 1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h102 (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) sK1]
    conv => enter [1, 2, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h9 (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 1]; rw [h3 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h261 ((sK0 ◇ sK0) ◇ sK1) sK0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

end Order3
