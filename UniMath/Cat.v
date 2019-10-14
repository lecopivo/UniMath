
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Inductive Cat :=
| SSet   : Cat
| Diff   : Cat
| Aff    : Cat
| Vec    : Cat
| Field  : Cat.

Inductive Ob : Cat -> Type :=
| indexed_object : forall (C : Cat), nat -> Ob C
| hom_object     : forall (C : Cat), Ob C -> Ob C -> Ob C

| vec_tensor_obj : Ob Vec -> Ob Vec -> Ob Vec
| aff_tensor_obj : Ob Vec -> Ob Vec -> Ob Vec

| product_obj    : Ob SSet -> Ob SSet -> Ob SSet
| biproduct_obj  : Ob Vec -> Ob Vec  -> Ob Vec

| 𝕆: Ob Vec
| ℝ : Ob Field

| forget_Field_to_Vec : Ob Field -> Ob Vec
| forget_Vec_to_Aff   : Ob Vec   -> Ob Aff
| forget_Aff_to_Diff  : Ob Aff   -> Ob Diff
| forget_Diff_to_SSet : Ob Diff  -> Ob SSet.

Notation "X - C -> Y" := (hom_object C X Y) (at level 55).
Notation "X ⊗ Y" := (vec_tensor_obj X Y).
Notation "X ⊠ Y" := (aff_tensor_obj X Y).
Notation "X × Y" := (product_obj X Y).
Notation "X ⊕ Y" := (biproduct_obj X Y).

Coercion Ob: Cat >-> Sortclass.

Inductive elem : forall (C : Cat), Ob C -> Type :=
  | hoh : forall (C : Cat), elem C (indexed_object C 0).
  | zero :
