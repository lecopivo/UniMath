
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.limits.products.

Print Sorted Universes.

Inductive Cat :=
| Diff   : Cat
| Vec    : Cat.

Inductive Ob : Cat -> Type :=
| indexed_object : nat -> Ob Vec
| hom            : Cat -> Ob Vec -> Ob Vec -> Ob Vec

| tensor_obj   : Ob Vec -> Ob Vec -> Ob Vec
| product_obj  : Ob Vec -> Ob Vec -> Ob Vec

| 𝕆: Ob Vec
| ℝ : Ob Vec.

Notation "X ~ C ~> Y" := (hom C X Y) (at level 55).

Notation "X --> Y" := (hom Vec  X Y) (at level 55).
Notation "X ~~> Y" := (hom Diff X Y) (at level 55).
Notation "X ⊗ Y"   := (tensor_obj  X Y).
Notation "X ⊕ Y"   := (product_obj X Y).

Coercion Ob: Cat >-> Sortclass.

Definition cat_or (gC fC : Cat) : Cat :=
  match gC with
  | Diff => Diff
  | Vec  => match fC with
            | Diff => Diff
            | Vec => Vec
            end
  end.

Notation "C ∨ D" := (cat_or C D).

Inductive elem : forall {C : Cat}, Ob C -> Type :=
| indexed_element  : forall (X : Vec) , nat -> elem X
| indexed_morphism : forall (C : Cat), forall (X Y : Vec), nat -> elem (hom C X Y)

| morphism_map : forall {C : Cat}, forall {X Y : Vec}, elem (hom C X Y) -> (elem X -> elem Y)

(* ----------------- Combinators ----------------- *)
(* Basic ones *)
| identity : forall {X : Vec}, elem (X --> X)
| compose  : forall {gC fC : Cat}, forall {X Y Z : Vec},
      elem (hom fC (hom gC X Y) (hom Vec (hom fC Y Z) (hom (cat_or gC fC) X Z)))
(* The above is a quite cryptic, it basically expands to the following: *)
(* ((X --> Y) --> ((Y --> Z) --> (X --> Z))) *)
(* ((X ~~> Y) --> ((Y --> Z) --> (X ~~> Z))) *)
(* ((X --> Y) ~~> ((Y ~~> Z) --> (X ~~> Z))) *)
(* ((X ~~> Y) ~~> ((Y ~~> Z) --> (X ~~> Z))) *)

| forget : forall {X Y : Vec},
    elem ((X --> Y) --> (X ~~> Y))

(* Vector Tensor product *)
| tensor_fmap   : forall {X X' Y Y' : Vec},
    elem ((X --> Y) --> ((X' --> Y') --> (X ⊗ X' --> Y ⊗ Y')))
| tensor_assoc  : forall {X Y Z : Vec},
    elem ((X ⊗ Y) ⊗ Z --> X ⊗ (Y ⊗ Z))
| tensor_unitor : forall {X : Vec},
    elem (ℝ ⊗ X --> X)

(* Cartesian product *)
| product_fmap : forall {C C' : Cat}, forall {X X' Y Y' : Vec},
      elem ((hom C X Y) --> ((hom C' X' Y') --> (hom (cat_or C C') (X ⊕ X')  (Y ⊕ Y'))))
| proj1 : forall {X Y : Vec},
    elem ((X ⊕ Y) --> X)
| proj2 : forall {X Y : Vec},
    elem ((X ⊕ Y) --> Y)
| injc1 : forall {X Y : Vec},
    elem (X --> (X ⊕ Y))
| injc2 : forall {X Y : Vec},
    elem (Y --> (X ⊕ Y))

(* Closed monoidal *)
| pair : forall {X Y : Vec},
    elem (X ~~> (Y ~~> (X ⊕ Y)))
| eval : forall {X Y : Vec},
    elem (((X ~~> Y) ⊕ X) ~~> Y)

| tpair : forall {X Y : Vec},
    elem (X --> (Y --> (X ⊗ Y)))
| teval : forall {X Y : Vec},
    elem (((X --> Y) ⊗ X) --> Y)

(* Symmetric category *)
| swap_args : forall {C D : Cat}, forall {X Y Z : Vec},
      elem ((hom C X (hom D Y Z)) --> (hom D Y (hom C X Z)))

(* Diagonal *)
| diag : forall {X : Vec},
    elem (X --> X ⊕ X)
| tdiag : forall {X : Vec},
    elem (X ~~> X ⊗ X)

(* Vector operations *)
| reals_one : elem ℝ
| vec_zero : forall {X : Vec},
    elem X
| vec_neg  : forall {X : Vec},
    elem (X --> X)
| vec_add   : forall {X : Vec},
    elem (X ⊕ X --> X)
| vec_mul   : forall {X : Vec},
    elem (ℝ ⊕ X --> X)

(* Differentiation *)
| grad : forall {X Y : Vec},
    elem ((X ~~> Y) --> (X ~~> (X --> Y))).

Coercion elem: Ob >-> Sortclass.

(* ------------------- EXTRA DEFINITIONS AND NOTATIONS ------------------------- *)

Notation "f [ x ]"   := (morphism_map f x) (at level 5).
Notation "( x , y )" := pair[x][y].
Notation "⟪ x , y ⟫" := tpair[x][y].
Notation "f ∘ g"     := compose[g][f].
Notation  "f ⊗⊗ g"   := tensor_fmap[f][g] (at level 50, left associativity).
Notation  "f ⊕⊕ g"   := product_fmap[f][g] (at level 50, left associativity).
Notation  "x + y"    := vec_add[(x,y)].
Notation  "s · x"    := vec_mul[(s,x)].
Notation   "- x"     := vec_neg[x].
Notation    "0"      := vec_zero.
Notation    "1"      := reals_one.

Notation "-∘ g" := compose[g]                 (at level 50).
Notation "f ∘-" := swap_args[compose][f]      (at level 50).
Notation "-⊗ g" := swap_args[tensor_fmap][g]  (at level 50).
Notation "f ⊗-" := tensor_fmap[f]             (at level 50).

(* Definition curry {X Y Z : Ab} : (X ⊗ Y --> Z) --> (X --> (Y --> Z)) := (eval ∘- ∘-)∘(tensor_assoc∘- ∘-)∘((@pair _ Y)∘-)∘(@pair (X ⊗ Y --> Z) X). *)
(* Definition uncurry {X Y Z : Ab} : (X --> (Y --> Z)) --> (X ⊗ Y --> Z) :=  (eval∘-) ∘ (-⊗(identity Y)). *)

(* Definition pair' {X Y : Ab} : Y --> (X --> (X ⊗ Y)) := swap_args[(@pair X Y)]. *)
(* Definition tsym  {X Y : Ab} : X ⊗ Y --> Y ⊗ X := uncurry[pair']. *)
(* Definition eval' {X Y : Ab} : X ⊗ (X --> Y) --> Y := eval ∘ tsym. *)

Notation curry   := ((teval ∘- ∘-) ∘ (tensor_assoc ∘- ∘-) ∘ (tpair ∘-) ∘ tpair).
Notation uncurry := ((teval∘-) ∘ (-⊗ identity)).

Notation tpair' := swap_args[tpair].
Notation tsym  := uncurry[tpair'].
Notation teval' := (teval ∘ tsym).

Definition zero (X : Vec)  := @vec_zero X.

(* ------------------- EXTRA AXIOMS -------------------------------------- *)

Axiom morphisms_equal_on_elements :
  forall {C : Cat},
  forall {X Y : Vec},
  forall {f g : (hom C X Y)},
    (forall (x : X), f[x]=g[x]) -> f = g.

Axiom morphisms_equal_on_product_elements :
  forall {C : Cat},
  forall {X Y Z : Vec},
  forall {f g : hom C (X ⊗ Y) Z},
    (forall (x : X), forall (y : Y), f[⟪x,y⟫]=g[⟪x,y⟫]) -> f = g.

(* ------------------- COMBINATORS RULES ON ELEMENTS --------------------- *)

(* identity *)
Axiom on_elements_identity :
  forall (X : Vec), forall (x : X),
      identity[x] = x.

(* compose *)
Axiom on_elements_compose :
  forall {C D : Cat}, forall {X Y Z : Vec},
      forall (g : hom C X Y), forall (f : hom D Y Z),
          forall (x : X),
            (f ∘ g)[x] = f[g[x]].

(* forget *)
Axiom on_elements_forget : forall {X Y : Vec}, forall (f : X --> Y), forall (x : X),
        forget[f][x] = f[x].

(* tensor_fmap *)
Axiom on_elements_tensor_fmap :
  forall {X X' Y Y' : Vec},
  forall (f : X --> Y), forall(f' : X' --> Y'),
      forall (x : X), forall (x' : X'),
          (f ⊗⊗ f')[⟪x,x'⟫] = ⟪f[x],f'[x']⟫.

(* tensor_assoc *)
Axiom on_elements_tensor_assoc :
  forall {X Y Z : Vec}, forall (x : X), forall (y : Y), forall (z : Z),
          tensor_assoc[⟪⟪x,y⟫,z⟫] = ⟪x,⟪y,z⟫⟫.

(* tensor_unitor *)
Axiom on_elements_tensor_unitor : forall {X : Vec}, forall (x : X), forall (s : ℝ),
        tensor_unitor[⟪s,x⟫] = s · x.

(* pair & eval *)
(* 1 = ε ∘ F η *)
(* eval ∘ (pair ⊗⊗ (identity Y)) = identity (X ⊗ Y) *)
(* Axiom on_elements_pair_eval_adjunction_1 *)
Axiom on_elements_pair : forall {X Y Z : Vec}, forall (x : X ⊕ Y),
      eval [(pair ⊕⊕ identity) [x]] = x.

(* pair & eval *)
(* 1 = G ε ∘ η *)
(* (eval∘-) ∘ pair = identity (X --> Y) *)
Axiom on_elements_eval : forall {X Y : Vec}, forall (f : X ~~> Y), forall (x : X),
        eval[(f,x)] = f[x].

(* pair & eval *)
(* 1 = ε ∘ F η *)
(* eval ∘ (pair ⊗⊗ (identity Y)) = identity (X ⊗ Y) *)
(* Axiom on_elements_pair_eval_adjunction_1 *)
Axiom on_elements_tpair : forall {X Y Z : Vec}, forall (x : X ⊗ Y),
      teval [(tpair ⊗⊗ identity) [x]] = x.

(* pair & eval *)
(* 1 = G ε ∘ η *)
(* (eval∘-) ∘ pair = identity (X --> Y) *)
Axiom on_elements_teval : forall {X Y : Vec}, forall (f : X --> Y), forall (x : X),
        teval[⟪f,x⟫] = f[x].

(* swap_args *)
Axiom on_elements_swap_args :
  forall {C D : Cat}, forall {X Y Z: Vec},
      forall (f : hom C X (hom D Y Z)),
      forall (x : X), forall (y : Y),
          swap_args[f][y][x] = f[x][y].

(* product_fmap *)
Axiom on_elements_product_fmap :
  forall {C C' : Cat}, forall {X X' Y Y' : Vec},
      forall (f : hom C X Y), forall (f' : hom C' X' Y'),
          forall (x : X), forall (x' : X'),
              (f ⊕⊕ f')[(x,x')] = (f[x], f'[x']).

(* proj1 *)
Axiom on_elements_proj1 : forall {X Y: Vec}, forall (x : X), forall (y : Y),
        proj1[(x,y)] = x.

(* proj2 *)
Axiom on_elements_proj2 : forall {X Y: Vec}, forall (x : X), forall (y : Y),
        proj2[(x,y)] = y.

(* injc1 *)
Axiom on_elements_injc1 : forall {X Y: Vec}, forall (x : X),
      injc1[x] = (x, zero Y).

(* injc2 *)
Axiom on_elements_injc2 : forall {X Y: Vec}, forall (y : X),
      injc2[y] = (zero X, y).

(* group_zero *)
Axiom on_elements_vec_zero : forall {X : Vec}, forall (x : X),
      x + 0 = x.

(* group_inv *)
Axiom on_elements_vec_neg : forall {X : Vec}, forall (x : X),
      x + (-x) = 0.

(* group_op - associativity *)
Axiom on_elements_vec_add_assoc : forall {X : Vec}, forall (x y z: X),
      (x + y) + z = x + (y + z).

(* group_op - commutativity *)
Axiom on_elements_vec_add_commut : forall {X : Vec}, forall (x y: X),
      x + y = y + x.

Axiom on_elements_vec_mul : forall {X : Vec}, forall (x y : X), forall (s : ℝ),
        s · (x + y) = s · x + s · y.

Axiom on_elements_vec_mul_zero : forall {X : Vec}, forall (x : X),
      0 · x = 0.

Axiom on_elements_vec_mul_one : forall {X : Vec}, forall (x y : X), forall (s : ℝ),
        1 · x = x.

Axiom on_elements_vec_add_morph : forall {C : Cat}, forall {X Y : Vec}, forall (f g : hom C X Y), forall (x : X),
          (f + g)[x] = f[x] + g[x].

Axiom on_elements_vec_mul_morph : forall {C : Cat}, forall {X Y : Vec}, forall (f : hom C X Y), forall (x : X), forall (s : ℝ),
            (s · f)[x] = s · f[x].

(* ----------------------- Vector Morphism rules ----------------------------- *)

Axiom on_elements_vec_morph_add : forall {X Y : Vec}, forall (f : X --> Y), forall (x y : X),
        f[x + y] = f[x] + f[y].

Axiom on_elements_vec_morph_mul : forall {X Y : Vec}, forall (f : X --> Y), forall (x : X), forall (s : ℝ),
          f[s · x] = s · f[x].

(* ----------------------- Doodle -------------------------------- *)

Variable X Y Z: Vec.

Variable g : X --> Y.
Variable f : Y --> Z.

(* Notation curry   := ((eval ∘- ∘-) ∘ (tensor_assoc ∘- ∘-) ∘ (pair ∘-) ∘ pair). *)
(* Notation uncurry := ((eval∘-) ∘ (-⊗ identity)). *)

(* Notation pair' := swap_args[pair]. *)
(* Notation tsym  := uncurry[pair']. *)
(* Notation eval' := (eval ∘ tsym). *)

Check (@identity (X⊗Y)).

Check (f ∘-)[g].
Check f ∘ g.

Lemma curry_identity : forall (X Y : Vec), curry[(@identity (X⊗Y))] = tpair.
Proof.
  intros.
  repeat (apply morphisms_equal_on_elements; intros).
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  repeat rewrite on_elements_swap_args.
  repeat rewrite on_elements_compose.
  rewrite on_elements_tensor_assoc.
  rewrite on_elements_teval.
  rewrite on_elements_identity.
  auto.
Qed.
