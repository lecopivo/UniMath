Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Variable Ab : UU.

Variable unit_object      : Ab.

Variable hom_object       : Ab -> Ab -> Ab.
Variable biproduct_object : Ab -> Ab -> Ab.
Variable tensor_object    : Ab -> Ab -> Ab.

Notation I := unit_object.
Notation "X --> Y" := (hom_object X Y).
Notation "X ⊕ Y"   := (biproduct_object X Y).
Notation "X ⊗ Y"   := (tensor_object X Y).

(* Elements *)

Variable elem : Ab -> UU.
Coercion elem : Ab >-> UU.

Variable morphism_to_fun : forall {X Y : Ab},  (X --> Y) -> (X -> Y).
Notation "f [ x ]" := (morphism_to_fun f x) (at level 5).

Axiom morphisms_equal_on_elements : forall {X Y : Ab}, forall {f g : X --> Y}, (forall (x : X), f[x]=g[x]) -> f = g.

(* ------------------- BASIC "COMBINATORS" --------------------- *)

(* When exporting to another language, you have to implement these combinators there *)
(* You also have to make sure that they satisfy rules that will be give later on *)

(*  _    _         _   _ _ *)
(* (_)__| |___ _ _| |_(_) |_ _  _ *)
(* | / _` / -_) ' \  _| |  _| || | *)
(* |_\__,_\___|_||_\__|_|\__|\_, | *)
(*                           |__/ *)

Variable identity : forall (X : Ab), X --> X.

(*                            _ _   _ *)
(*  __ ___ _ __  _ __  ___ __(_) |_(_)___ _ _ *)
(* / _/ _ \ '  \| '_ \/ _ (_-< |  _| / _ \ ' \ *)
(* \__\___/_|_|_| .__/\___/__/_|\__|_\___/_||_| *)
(*              |_| *)

Variable compose : forall {X Y Z}, (X --> Y) --> ((Y --> Z) --> (X --> Z)).

(*                                        _ *)
(*  __ _  _ _ _ _ _ _  _     _____ ____ _| | *)
(* / _| || | '_| '_| || |   / -_) V / _` | | *)
(* \__|\_,_|_| |_|  \_, |   \___|\_/\__,_|_| *)
(*                  |__/ *)

Variable pair : forall {X Y : Ab}, X --> (Y --> X ⊗ Y).
Variable eval  : forall {X Y : Ab}, (X --> Y) ⊗ X --> Y.

(* pair and eval are counit and unit of adjunction between tensor and hom functors *)
(* pair will be defined as currying of (identity (X⊗Y)) *)

(*  _                                           _         _ *)
(* | |_ ___ _ _  ___ ___ _ _   _ __ _ _ ___  __| |_  _ __| |_ *)
(* |  _/ -_) ' \(_-</ _ \ '_| | '_ \ '_/ _ \/ _` | || / _|  _| *)
(*  \__\___|_||_/__/\___/_|   | .__/_| \___/\__,_|\_,_\__|\__| *)
(*                            |_| *)

Variable swap_args : forall {X Y Z : Ab}, (X --> (Y --> Z)) --> (Y --> (X --> Z)).
(* Variable tsym : forall {X Y : Ab}, (X ⊗ Y) --> (Y ⊗ X). *)
Variable tensor_fmap : forall {X X' Y Y' : Ab}, (X --> Y) --> ((X' --> Y') --> (X ⊗ X' --> Y ⊗ Y')).

Variable tensor_assoc  : forall {X Y Z : Ab}, (X ⊗ Y) ⊗ Z --> X ⊗ (Y ⊗ Z).
Variable tensor_unitor : forall {X : Ab}, I ⊗ X --> X.

(*  _    _                  _         _ *)
(* | |__(_)_ __ _ _ ___  __| |_  _ __| |_ *)
(* | '_ \ | '_ \ '_/ _ \/ _` | || / _|  _| *)
(* |_.__/_| .__/_| \___/\__,_|\_,_\__|\__| *)
(*        |_| *)
Variable biproduct_pair : forall {X Y : Ab}, X -> Y -> X ⊕ Y.

Variable proj1 : forall {X Y : Ab}, X ⊕ Y --> X.
Variable proj2 : forall {X Y : Ab}, X ⊕ Y --> Y.
Variable injc1 : forall {X Y : Ab}, X --> X ⊕ Y.
Variable injc2 : forall {X Y : Ab}, Y --> X ⊕ Y.

(*                                                  _   _ *)
(*  __ _ _ _ ___ _  _ _ __   ___ _ __  ___ _ _ __ _| |_(_)___ _ _  ___ *)
(* / _` | '_/ _ \ || | '_ \ / _ \ '_ \/ -_) '_/ _` |  _| / _ \ ' \(_-< *)
(* \__, |_| \___/\_,_| .__/ \___/ .__/\___|_| \__,_|\__|_\___/_||_/__/ *)
(* |___/             |_|        |_| *)

Variable group_zero : forall {X : Ab}, X.
Variable group_inv  : forall {X : Ab}, X --> X.
Variable group_op   : forall {X : Ab}, X ⊕ X --> X.

(* ------------------- EXTRA DEFINITIONS AND NOTATIONS ------------------------- *)

Notation "( x , y )" := (biproduct_pair x y).
Notation "⟪ x , y ⟫" := pair[x][y].
Notation  "f ∘ g"    := compose[g][f].
Notation  "f ⊗⊗ g"   := tensor_fmap[f][g] (at level 50, left associativity).
Notation  "x + y"    := group_op[(x,y)].
Notation   "- x"     := group_inv[x].
Notation    "0"      := group_zero.

Definition compose_right {X Y Z : Ab} := (@compose X Y Z).
Definition compose_left  {X Y Z : Ab} := (swap_args[(@compose X Y Z)]).
Definition tensor_fmap_right {X X' Y Y' : Ab} := swap_args[(@tensor_fmap X X' Y Y')].
Definition tensor_fmap_left  {X X' Y Y' : Ab} := (@tensor_fmap X X' Y Y').

Notation "Z -∘ g" := (@compose_right _ _ Z)[g] (at level 50).
Notation "f ∘- X" := (@compose_left  X _ _)[f] (at level 50).

Notation "-∘ g" := compose_right[g] (at level 50).
Notation "f ∘-" := compose_left[f] (at level 50).
Notation "-⊗ g" := tensor_fmap_right[g] (at level 50).
Notation "f ⊗-" := tensor_fmap_left[f] (at level 50).

Definition curry {X Y Z : Ab} : (X ⊗ Y --> Z) --> (X --> (Y --> Z)) := (eval ∘- ∘-)∘(tensor_assoc∘- ∘-)∘((@pair _ Y)∘-)∘(@pair (X ⊗ Y --> Z) X).
Definition uncurry {X Y Z : Ab} : (X --> (Y --> Z)) --> (X ⊗ Y --> Z) :=  (eval∘-) ∘ (-⊗(identity Y)).

Definition zero (X : Ab)  := @group_zero X.
Definition ident (X : Ab) := @identity X.

(* ------------------- COMBINATORS RULES ON ELEMENTS --------------------- *)

(* identity *)
Axiom on_elements_identity : forall (X : Ab), forall (x : X),
      (identity X)[x] = x.

(* compose *)
Axiom on_elements_compose : forall {X Y Z}, forall (g : X --> Y), forall (f : Y --> Z), forall (x : X),
          (f ∘ g)[x] = f[g[x]].

(* pair - there is no meaning fulld definition on elements *)
(* eval *)
Axiom on_elements_eval : forall (X Y : Ab), forall (f : X --> Y), forall (x : X),
        eval[⟪f,x⟫] = f[x].

(* swap_args *)
Axiom on_elements_swap_args : forall {X Y Z: Ab}, forall (f : X --> (Y --> Z)), forall (x : X), forall (y : Y),
          swap_args[f][y][x] = f[x][y].

(* tensor_fmap *)
Axiom on_elements_tensor_fmap : forall {X X' Y Y' : Ab}, forall (f : X --> Y), forall(f' : X' --> Y'), forall (x : X), forall (x' : X'),
            (f ⊗⊗ f')[⟪x,x'⟫] = ⟪f[x],f'[x']⟫.

(* tensor_assoc *)
Axiom on_elements_tensor_assoc : forall {X Y Z : Ab}, forall (x : X), forall (y : Y), forall (z : Z),
          tensor_assoc[⟪⟪x,y⟫,z⟫] = ⟪x,⟪y,z⟫⟫.

(* tensor_unitor *)
Axiom on_elements_tensor_unitor : forall {X : Ab}, forall (x : X), forall (i : I),
        tensor_unitor[⟪i,x⟫] = x.

(* proj1 *)
Axiom on_elements_proj1 : forall {X Y: Ab}, forall (x : X), forall (y : Y),
        proj1[(x,y)] = x.

(* proj2 *)
Axiom on_elements_proj2 : forall {X Y: Ab}, forall (x : X), forall (y : Y),
        proj2[(x,y)] = y.

(* injc1 *)
Axiom on_elements_injc1 : forall {X Y: Ab}, forall (x : X),
      injc1[x] = (x, zero Y).

(* injc2 *)
Axiom on_elements_injc2 : forall {X Y: Ab}, forall (y : X),
      injc2[y] = (zero X, y).

(* group_zero *)
Axiom on_elements_group_zero : forall {X : Ab}, forall (x : X),
      x + 0 = x.

(* group_inv *)
Axiom on_elements_group_inv : forall {X : Ab}, forall (x : X),
      x + (-x) = 0.

(* group_op - associativity *)
Axiom on_elements_group_op_assoc : forall {X : Ab}, forall (x y z: X),
      (x + y) + z = x + (y + z).

(* group_op - commutativity *)
Axiom on_elements_group_op_commut : forall {X : Ab}, forall (x y: X),
      x + y = y + x.

Axiom on_elements_group_op_morph : forall {X Y : Ab}, forall (f g : X --> Y), forall (x : X),
        (f + g)[x] = f[x] + g[x].

(* -------------- COMBINATORS IDENTITIES ---------------- *)

Lemma identity_compose_identity : forall {X Y : Ab}, forall (f : X --> Y),
      f ∘ (identity X) = f
      /\
      (identity Y) ∘ f = f.
Proof.
  intros. split.
  apply morphisms_equal_on_elements. intros.
  rewrite on_elements_compose.
  rewrite on_elements_identity. auto.
  apply morphisms_equal_on_elements. intros.
  rewrite on_elements_compose.
  rewrite on_elements_identity. auto.
Qed.

Lemma identity_compose_assoc : forall {W X Y Z : Ab}, forall (h : W --> X), forall (g : X --> Y), forall (f : Y --> Z),
          (f∘g)∘h = f∘(g∘h).
Proof.
  intros.
  apply morphisms_equal_on_elements. intros.
  repeat rewrite on_elements_compose. auto.
Qed.

Lemma identity_apply_post_compose : forall {X Y Z : Ab}, forall (g : X --> Y), forall (f : Y --> Z),
        (f∘-)[g] = f∘g.
Proof.
  intros.
  unfold compose_left.
  repeat rewrite on_elements_swap_args.
  auto.
Qed.

Definition pair' {X Y : Ab} : Y --> (X --> (X ⊗ Y)) := swap_args[(@pair X Y)].
Definition tsym  {X Y : Ab} : X ⊗ Y --> Y ⊗ X := uncurry[pair'].
Definition eval' {X Y : Ab} : X ⊗ (X --> Y) --> Y := eval ∘ tsym.

(* Lemma identity_eval_pair_1 : forall {X Y : Ab}, *)
(*     eval ∘ (pair ⊗⊗ (identity Y)) = identity (X ⊗ Y). *)
(* Proof. *)
(*   intros. *)
(*   repeat (apply morphisms_equal_on_elements; intros). *)
(*   repeat rewrite on_elements_compose. *)

Lemma identity_eval_pair_2 : forall {X Y : Ab},
    (eval∘-) ∘ pair = identity (X --> Y).
Proof.
  intros.
  unfold compose_left.
  repeat (apply morphisms_equal_on_elements; intros).
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.




Lemma identity_adsf : forall {X Y : Ab},
    eval' ∘ ((identity X) ⊗⊗ pair') = identity (X ⊗ Y).
Proof.
  intros.
  repeat (unfold pair'; unfold eval'; unfold tsym; unfold uncurry).
  repeat rewrite on_elements_compose.
  repeat rewrite identity_compose_assoc.


Lemma identity_adsf : forall {X Y : Ab},
    (eval'∘-) ∘ pair' = identity (X-->Y).
Proof.
  intros.
  repeat (unfold pair'; unfold eval'; unfold tsym; unfold uncurry).
  repeat rewrite on_elements_compose.

  repeat (rewrite on_elements_identity;
          rewrite on_elements_compose;
          rewrite on_elements_swap_args).



Lemma identity_compose_post_compose : forall {W X Y Z : Ab}, forall (g : X --> Y), forall (f : Y --> Z),
      (f∘-)∘(g∘-) = (f∘g)∘-W.
Proof.
  intros.
  repeat (apply morphisms_equal_on_elements; intros).
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  auto.
Qed.



Lemma identity_curry_uncurry : forall {X Y Z : Ab},
    curry ∘ uncurry = identity (X --> (Y --> Z)).
Proof.
  intros.
  repeat (apply morphisms_equal_on_elements; intros).
  unfold uncurry.
  unfold curry.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_assoc.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_identity.
  auto.
Qed.

Lemma idenity_uncurry_curr : forall {X Y Z : Ab},
    uncurry ∘ curry = identity (X ⊗ Y --> Z).
Proof.
  intros.
  unfold uncurry.
  unfold curry.
  repeat rewrite <- identity_compose_assoc.
  repeat rewrite indentity_compose_post_compose.
  repeat (apply morphisms_equal_on_elements; intros).
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite <- identity_compose_assoc.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tsym.
  repeat rewrite on_elements_swap_args.

  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_curry.
  repeat rewrite on_elements_compose.

  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_identity.
  auto.

Variable curry : forall {X Y Z : Ab}, (X ⊗ Y --> Z) --> (X --> (Y --> Z)).
Variable eval  : forall {X Y : Ab}, (X --> Y) ⊗ X --> Y.

(* Variable pair : forall {X Y : Ab}, X --> (Y --> X ⊗ Y). *)

(* pair and eval are counit and unit of adjunction between tensor and hom functors *)
(* pair will be defined as currying of (identity (X⊗Y)) *)

(*  _                                           _         _ *)
(* | |_ ___ _ _  ___ ___ _ _   _ __ _ _ ___  __| |_  _ __| |_ *)
(* |  _/ -_) ' \(_-</ _ \ '_| | '_ \ '_/ _ \/ _` | || / _|  _| *)
(*  \__\___|_||_/__/\___/_|   | .__/_| \___/\__,_|\_,_\__|\__| *)
(*                            |_| *)

Variable tsym : forall {X Y : Ab}, (X ⊗ Y) --> (Y ⊗ X).
Variable tensor_fmap : forall {X X' Y Y' : Ab}, (X --> Y) ⊗ (X' --> Y') --> (X ⊗ X' --> Y ⊗ Y').

Variable tensor_assoc  : forall {X Y Z : Ab}, (X ⊗ Y) ⊗ Z --> X ⊗ (Y ⊗ Z).
Variable tensor_unitor : forall {X : Ab}, I ⊗ X --> X.

(*  _    _                  _         _ *)
(* | |__(_)_ __ _ _ ___  __| |_  _ __| |_ *)
(* | '_ \ | '_ \ '_/ _ \/ _` | || / _|  _| *)
(* |_.__/_| .__/_| \___/\__,_|\_,_\__|\__| *)
(*        |_| *)

Variable biproduct_pair : forall {X Y : Ab}, X -> Y -> X ⊕ Y.

Variable proj1 : forall {X Y : Ab}, X ⊕ Y --> X.
Variable proj2 : forall {X Y : Ab}, X ⊕ Y --> Y.
Variable injc1 : forall {X Y : Ab}, X --> X ⊕ Y.
Variable injc2 : forall {X Y : Ab}, Y --> X ⊕ Y.

(*                                                  _   _ *)
(*  __ _ _ _ ___ _  _ _ __   ___ _ __  ___ _ _ __ _| |_(_)___ _ _  ___ *)
(* / _` | '_/ _ \ || | '_ \ / _ \ '_ \/ -_) '_/ _` |  _| / _ \ ' \(_-< *)
(* \__, |_| \___/\_,_| .__/ \___/ .__/\___|_| \__,_|\__|_\___/_||_/__/ *)
(* |___/             |_|        |_| *)

Variable group_zero : forall {X : Ab}, X.
Variable group_inv  : forall {X : Ab}, X --> X.
Variable group_op   : forall {X : Ab}, X ⊕ X --> X.
