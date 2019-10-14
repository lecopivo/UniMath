
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Print Sorted Universes.

Inductive Cat :=
| Diff   : Cat
| Aff    : Cat
| Vec    : Cat.

Inductive Ob : Cat -> Type :=
| indexed_object : forall (C : Cat), nat -> Ob C
| hom_object     : forall {C : Cat}, Ob C -> Ob C -> Ob C

| tensor_obj   : forall {C : Cat}, Ob C -> Ob C -> Ob C
| product_obj  : forall {C : Cat}, Ob C -> Ob C -> Ob C
| tensor_unit  : forall {C : Cat}, Ob C

| tangent_bundle : Ob Diff -> Ob Diff

| 𝕆: Ob Vec
| ℝ : Ob Vec

| forget_Vec_to_Aff   : Ob Vec -> Ob Aff
| forget_Aff_to_Diff  : Ob Aff -> Ob Diff.

Notation "X --> Y" := (hom_object X Y) (at level 55).
Notation "X ⊗ Y" := (tensor_obj  X Y).
Notation "X × Y" := (product_obj X Y).

Coercion Ob: Cat >-> Sortclass.

(* Does this work? - I want automatic application of these forgetful functors. *)
Coercion forget_Vec_to_Aff:   Ob >-> Ob.
Coercion forget_Aff_to_Diff:  Ob >-> Ob.

Inductive elem : forall {C : Cat}, Ob C -> Type :=
| indexed_element  : forall {C : Cat}, forall (X : C) , nat -> elem X
| indexed_morphism : forall {C : Cat}, forall (X Y : C), nat -> elem (X --> Y)

| morphism_map : forall {C : Cat}, forall {X Y : C}, elem (X --> Y) -> (elem X -> elem Y)

(* ----------------- Combinators ----------------- *)
(* Basic ones *)
| identity : forall {C : Cat}, forall {X : C}, elem (X --> X)
| compose  : forall {C : Cat}, forall {X Y Z : C}, elem ((X --> Y) --> ((Y --> Z) --> (X --> Z)))

(* Vector Tensor product *)
| tensor_fmap   : forall {X X' Y Y' : Vec},
    elem ((X --> Y) --> ((X' --> Y') --> (X ⊗ X' --> Y ⊗ Y')))
| tensor_assoc  : forall {X Y Z : Vec},
    elem ((X ⊗ Y) ⊗ Z --> X ⊗ (Y ⊗ Z))
| tensor_unitor : forall {X : Vec},
    elem (tensor_unit ⊗ X --> X)

(* Affine tensor has projections *)
| aproj1 : forall {X Y : Aff},
   elem (X ⊗ Y --> X)
| aproj2 : forall {X Y : Aff},
    elem (X ⊗ Y --> Y)

(* Diff tensor has projections and diagonal *)
| dproj1 : forall {X Y : Diff},
    elem (X ⊗ Y --> X)
| dproj2 : forall {X Y : Diff},
    elem (X ⊗ Y --> Y)
| tdiag : forall {X Y : Diff},
    elem (X --> X ⊗ X)

(* Cartesian product *)
| product_fmap : forall {C : Cat}, forall {X X' Y Y' : C},
    elem ((X --> Y) --> ((X' --> Y') --> (X × X' --> Y × Y')))
| proj1 : forall {C : Cat}, forall {X Y : C},
    elem ((X × Y) --> X)
| proj2 : forall {C : Cat}, forall {X Y : C},
    elem ((X × Y) --> Y)
| cdiag : forall {C : Cat}, forall {X : C},
    elem (X --> X × X)

(* Vector product has injections *)
| injc1 : forall {X Y : Vec},
    elem (X --> X × Y)
| injc2 : forall {X Y : Vec},
    elem (Y --> X × Y)

(* Closed monoidal *)
| pair      : forall {C : Cat}, forall {X Y : C},
    elem (X --> (Y --> (X ⊗ Y)))
| eval      : forall {C : Cat}, forall {X Y : C},
    elem ((X --> Y) ⊗ X --> Y)
| swap_args : forall {C : Cat}, forall {X Y Z : C},
      elem ((X --> (Y --> Z)) --> (Y --> (X --> Z)))

(* Group operations *)
| vec_zero : forall {X : Vec},
    elem X
| vec_neg  : forall {X : Vec},
    elem (X --> X)
| vec_add   : forall {X : Vec},
    elem (X × X --> X)
| vec_mul   : forall {X : Vec},
    elem (tensor_unit × X --> X)

(* Differentiation *)
| tangent_map : forall {X Y : Vec},
    elem ((X --> Y) --> (X × X --> Y × Y))
| grad : ,
    elem (tangent_bundle X --> X).
