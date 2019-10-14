
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Inductive direction := covar | contr.

Inductive Cat :=
| SSet : Cat
| Smooth : Cat
| Aff : Cat
| Vec : Cat
| Ab  : Cat
| Fun : direction -> Cat -> Cat -> Cat.

Notation "C = d => D"  := (Fun d C D) (at level 55).

Inductive ob : Cat -> Type :=
| indexed_object : forall (C : Cat), nat -> ob C

| hom            : forall (C : Cat),   ob (C =contr=> (C =covar=> SSet))

| functor_map    : forall {C D : Cat}, forall {d : direction}, ob (C =d=> D) -> (ob C -> ob D).

Coercion ob: Cat >-> Sortclass.

Notation "F ⦃ X ⦄" := (functor_map F X) (at level 5).
Notation "X --> Y" := ((hom _)⦃X⦄⦃Y⦄).
Definition X := indexed_object SSet 0.
Definition Y := indexed_object SSet 1.

Check X.
Check Y.

Check (hom SSet)⦃X⦄⦃Y⦄.
Check X --> Y.

Inductive elem : forall {C : Cat}, C -> Type :=
| indexed_element : forall (C : Cat), forall (X : C), elem X

| morphism_map : forall (C : Cat), forall (X Y : C), elem (X --> Y) -> elem X -> elem Y
| functor_fmap : forall {C D : Cat}, forall {d : direction}, forall (F : C =d=> D), forall {X Y : C}, forall (f : elem (X --> Y)), elem (F⦃X⦄ --> F⦃Y⦄).


Notation "X - C -> Y" := (hom_object C X Y) (at level 55).
Notation "X ⊗ Y" := (vec_tensor_obj X Y).
Notation "X ⊠ Y" := (aff_tensor_obj X Y).
Notation "X × Y" := (product_obj X Y).
Notation "X ⊕ Y" := (biproduct_obj X Y).

Coercion Ob: Cat >-> Sortclass.



Inductive Category : nat -> Type :=
| Cat2 : Category 3

with Object : forall (n : nat), Category n -> Type :=

  | indexed_object : forall (n : nat), forall (C : Category n), nat -> Object C.
