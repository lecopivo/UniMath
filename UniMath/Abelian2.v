Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Inductive Ab :=
| indexed_object   : Ab
| hom_object       : Ab -> Ab -> Ab
| tensor_object    : Ab -> Ab -> Ab
| biproduct_object : Ab -> Ab -> Ab
| unit             : Ab.

Notation "X --> Y" := (hom_object X Y).
Notation "X ⊗ Y"   := (tensor_object X Y).
Notation "X ⊕ Y"   := (biproduct_object X Y).
Notation I := unit.

Inductive elem : Ab -> Type :=
| indexed_element : forall (X : Ab), nat -> elem X
| morph_to_fun    : forall {X Y : Ab}, elem (X --> Y) -> (elem X -> elem Y)

(*----------------- Combinators -------------------*)
(* Basic ones *)
| identity : forall {X : Ab},
    elem (X --> X)
| compose  : forall {X Y Z : Ab},
    elem ((X --> Y) --> ((Y --> Z) --> (X --> Z)))

(* Tensor product *)
| tensor_fmap   : forall {X X' Y Y' : Ab},
    elem ((X --> Y) --> ((X' --> Y') --> (X ⊗ X' --> Y ⊗ Y')))
| tensor_assoc  : forall {X Y Z : Ab},
    elem ((X ⊗ Y) ⊗ Z --> X ⊗ (Y ⊗ Z))
| tensor_unitor : forall {X : Ab},
    elem (I ⊗ X --> X)

(* Closed Monoidal *)
| pair      : forall {X Y : Ab},
    elem (X --> (Y --> (X ⊗ Y)))
| eval      : forall {X Y : Ab},
    elem ((X --> Y) ⊗ X --> Y)
| swap_args : forall {X Y Z : Ab},
    elem ((X --> (Y --> Z)) --> (Y --> (X --> Z)))

(* Biproduct *)
| biproduct_pair : forall {X Y : Ab},
    elem X -> elem Y -> elem (X ⊕ Y)
| proj1 : forall {X Y : Ab},
    elem (X ⊕ Y --> X)
| proj2 : forall {X Y : Ab},
    elem (X ⊕ Y --> Y)
| injc1 : forall {X Y : Ab},
    elem (X --> X ⊕ Y)
| injc2 : forall {X Y : Ab},
    elem (Y --> X ⊕ Y)

(* Group operations *)
| group_zero : forall {X : Ab},
    elem X
| group_inv  : forall {X : Ab},
    elem (X --> X)
| group_op   : forall {X : Ab},
    elem (X ⊕ X --> X).

Coercion elem: Ab >-> Sortclass.

(* ------------------- EXTRA DEFINITIONS AND NOTATIONS ------------------------- *)

Notation "f [ x ]"   := (morph_to_fun f x) (at level 5).
Notation "( x , y )" := (biproduct_pair x y).
Notation "⟪ x , y ⟫" := pair[x][y].
Notation "f ∘ g"     := compose[g][f].
Notation  "f ⊗⊗ g"   := tensor_fmap[f][g] (at level 50, left associativity).
Notation  "x + y"    := group_op[(x,y)].
Notation   "- x"     := group_inv[x].
Notation    "0"      := group_zero.

Definition compose_right {X Y Z : Ab} := (@compose X Y Z).
Definition compose_left  {X Y Z : Ab} := (swap_args[(@compose X Y Z)]).
Definition tensor_fmap_right {X X' Y Y' : Ab} := swap_args[(@tensor_fmap X X' Y Y')].
Definition tensor_fmap_left  {X X' Y Y' : Ab} := (@tensor_fmap X X' Y Y').

Notation "Z -∘ g" := (@compose _ _ Z)[g]                   (at level 50).
Notation "f ∘- X" := (swap_args[(@compose_left X _ _)][f]) (at level 50).

Notation "-∘ g" := compose[g]                 (at level 50).
Notation "f ∘-" := swap_args[compose][f]      (at level 50).
Notation "-⊗ g" := swap_args[tensor_fmap][g]  (at level 50).
Notation "f ⊗-" := tensor_fmap[f]             (at level 50).

(* Definition curry {X Y Z : Ab} : (X ⊗ Y --> Z) --> (X --> (Y --> Z)) := (eval ∘- ∘-)∘(tensor_assoc∘- ∘-)∘((@pair _ Y)∘-)∘(@pair (X ⊗ Y --> Z) X). *)
(* Definition uncurry {X Y Z : Ab} : (X --> (Y --> Z)) --> (X ⊗ Y --> Z) :=  (eval∘-) ∘ (-⊗(identity Y)). *)

(* Definition pair' {X Y : Ab} : Y --> (X --> (X ⊗ Y)) := swap_args[(@pair X Y)]. *)
(* Definition tsym  {X Y : Ab} : X ⊗ Y --> Y ⊗ X := uncurry[pair']. *)
(* Definition eval' {X Y : Ab} : X ⊗ (X --> Y) --> Y := eval ∘ tsym. *)

Notation curry   := ((eval ∘- ∘-) ∘ (tensor_assoc ∘- ∘-) ∘ (pair ∘-) ∘ pair).
Notation uncurry := ((eval∘-) ∘ (-⊗ identity)).

Notation pair' := swap_args[pair].
Notation tsym  := uncurry[pair'].
Notation eval' := (eval ∘ tsym).


Definition zero (X : Ab)  := @group_zero X.

(* ------------------- EXTRA AXIOMS -------------------------------------- *)

Axiom morphisms_equal_on_elements : forall {X Y : Ab}, forall {f g : X --> Y}, (forall (x : X), f[x]=g[x]) -> f = g.
Axiom morphisms_equal_on_product_elements : forall {X Y Z : Ab}, forall {f g : X ⊗ Y --> Z}, (forall (x : X), forall (y : Y), f[⟪x,y⟫]=g[⟪x,y⟫]) -> f = g.

(* ------------------- COMBINATORS RULES ON ELEMENTS --------------------- *)

(* identity *)
Axiom on_elements_identity : forall (X : Ab), forall (x : X),
      identity[x] = x.

(* compose *)
Axiom on_elements_compose : forall {X Y Z}, forall (g : X --> Y), forall (f : Y --> Z), forall (x : X),
          (f ∘ g)[x] = f[g[x]].

(* pair & eval *)
(* 1 = ε ∘ F η *)
(* eval ∘ (pair ⊗⊗ (identity Y)) = identity (X ⊗ Y) *)
(* Axiom on_elements_pair_eval_adjunction_1 *)
Axiom on_elements_pair_eval_adjunction_1 : forall {X Y Z : Ab}, forall (x : X ⊗ Y),
      eval [(pair ⊗⊗ identity) [x]] = x.

(* pair & eval *)
(* 1 = G ε ∘ η *)
(* (eval∘-) ∘ pair = identity (X --> Y) *)
Axiom on_elements_eval : forall {X Y : Ab}, forall (f : X --> Y), forall (x : X),
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

(* ---------------- SOME IDENTITIES ------------------ *)

Lemma tensor_hom_adjunction_1 : forall {X Y Z : Ab},
      eval ∘ (pair ⊗⊗ identity) = (@identity (X ⊗ Y)).
Proof.
  intros.
  apply morphisms_equal_on_product_elements; intros.
  rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_identity.
  auto.
Qed.

Lemma tensor_hom_adjunction_2 : forall {X Y : Ab},
    eval' ∘ (identity ⊗⊗ pair') = (@identity (X ⊗ Y)).
Proof.
  intros.
  apply morphisms_equal_on_product_elements; intros.
  repeat (unfold compose_left; unfold tensor_fmap_right).
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_swap_args.
  auto.
Qed.

Lemma tensor_hom_adjunction_3 : forall {X Y : Ab},
    (eval'∘-) ∘ pair' = (@identity (X --> Y)).
Proof.
  intros.
  repeat (apply morphisms_equal_on_elements; intros).
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_identity.
  auto.
Qed.

Lemma identity_curry_uncurry : forall {X Y Z : Ab},
    curry ∘ uncurry = (@identity (X --> (Y --> Z))).
Proof.
  intros.
  repeat (apply morphisms_equal_on_elements; intros).
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

Lemma identity_uncurry_curry : forall {X Y Z : Ab},
    uncurry ∘ curry = (@identity (X ⊗ Y --> Z)).
Proof.
  intros.
  apply morphisms_equal_on_elements; intros.
  apply morphisms_equal_on_product_elements; intros.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_fmap.
  repeat rewrite on_elements_identity.
  repeat rewrite on_elements_eval.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_tensor_assoc.
  repeat rewrite on_elements_eval.
  auto.
Qed.
