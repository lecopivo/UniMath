(**

Syntax of Martin-Löf type theory a la "Constructive Mathematics and
Computer Programming" (1979)

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.arbitrary_products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseArbitraryProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseArbitraryCoproduct.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.ArbitrarySumOfSignatures.
Require Import UniMath.SubstitutionSystems.ProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.SigToMonad.
Require Import UniMath.SubstitutionSystems.GenSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial.

Infix "::" := (cons_list nat).
Notation "[]" := (nil_list nat) (at level 0, format "[]").
Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Section preamble.

Lemma isdecequnit : isdeceq unit.
Proof.
apply (isdeceqifisaprop _ isapropunit).
Defined.

Lemma isdeceqcoprod {A B : UU} (h1 : isdeceq A) (h2 : isdeceq B) :
  isdeceq (A ⨿ B).
Proof.
intros ab ab'.
induction ab as [a|b]; induction ab' as [a'|b'].
- induction (h1 a a') as [p|p].
+ apply inl, (maponpaths (@ii1 A B) p).
+ apply inr; intro H; apply (p (ii1_injectivity _ _ H)).
- apply inr, negpathsii1ii2.
- apply inr, negpathsii2ii1.
- induction (h2 b b') as [p|p].
+ apply inl, (maponpaths (@ii2 A B) p).
+ apply inr; intro H; apply (p (ii2_injectivity _ _ H)).
Defined.

Definition three_rec {A : UU} (a b c : A) : stn 3 -> A.
Proof.
induction 1 as [n p].
induction n as [_|n _]; [apply a|].
induction n as [_|n _]; [apply b|].
induction n as [_|n _]; [apply c|].
induction (nopathsfalsetotrue p).
Defined.

Definition four_rec {A : UU} (a b c d : A) : stn 4 -> A.
Proof.
induction 1 as [n p].
induction n as [_|n _]; [apply a|].
induction n as [_|n _]; [apply b|].
induction n as [_|n _]; [apply c|].
induction n as [_|n _]; [apply d|].
induction (nopathsfalsetotrue p).
Defined.

Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Definition ProductsHSET2 : Products HSET2.
Proof.
apply (Products_functor_precat _ _ ProductsHSET).
Defined.

Definition ArbitraryProductsHSET2 : ArbitraryProducts bool HSET2.
Proof.
apply (ArbitraryProducts_functor_precat _ _ _ (ArbitraryProducts_HSET bool)).
Defined.

Definition CoproductsHSET2 : Coproducts HSET2.
Proof.
apply (Coproducts_functor_precat _ _ CoproductsHSET).
Defined.

Lemma has_exponentials_HSET2 : has_exponentials ProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

Lemma InitialHSET2 : Initial HSET2.
Proof.
apply (Initial_functor_precat _ _ InitialHSET).
Defined.

(* Convenient function for combining decidability proofs and
   signatures *)
Definition SumGenSig {A B : UU} (p1 : isdeceq A × GenSig A)
  (p2 : isdeceq B × GenSig B) : isdeceq (A ⨿ B) × GenSig (A ⨿ B).
Proof.
split.
+ apply (isdeceqcoprod (pr1 p1) (pr1 p2)).
+ induction 1; [ apply (pr2 p1 a) | apply (pr2 p2 b) ].
Defined.

End preamble.

Infix "++" := SumGenSig.

Section MLTT79.

(** MLTT79:

Pi types           (Πx:A)B                     [0,1]
lambda             (λx)b                       [1]
application        (c)a                        [0,0]

Sigma types        (Σx:A)B                     [0,1]
pair               (a,b)                       [0,0]
pair-elim          (Ex,y)(c,d)                 [0,2]

Sum types          A + B                       [0,0]
inl                i(a)                        [0]
inr                j(b)                        [0]
sum-elim           (Dx,y)(c,d,e)               [0,1,1]

Id types           I(A,a,b)                    [0,0,0]
refl               r                           []
J                  J(c,d)                      [0,0]

Fin types          N_i                         []
Fin elems          0_i ... (i-1)_i             [] ... []    (i times)
Fin-elim           R_i(c,c_0,...,c_(i-1))      [0,0,...,0]  (i+1 zeroes)

Nat                N                           []
zero               0                           []
suc                a'                          [0]
nat-elim           (Rx,y)(c,d,e)               [0,0,2]

W-types            (Wx∈A)B                     [0,1]
sup                sup(a,b)                    [0,0]
W-elim             (Tx,y,z)(c,d)               [0,3]

Universes          U_0,U_1,...                 [],[],...

*)

Local Notation "[0]" := (0 :: []).
Local Notation "[1]" := (1 :: []).
Local Notation "[0,0]" := (0 :: 0 :: []).
Local Notation "[0,1]" := (0 :: 1 :: []).
Local Notation "[0,2]" := (0 :: 2 :: []).
Local Notation "[0,3]" := (0 :: 3 :: []).
Local Notation "[0,0,0]" := (0 :: 0 :: 0 :: []).
Local Notation "[0,0,2]" := (0 :: 0 :: 2 :: []).
Local Notation "[0,1,1]" := (0 :: 1 :: 1 :: []).

Definition PiSig : GenSig (stn 3) := three_rec [0,1] [1] [0,0].

Definition SigmaSig : GenSig (stn 3) := three_rec [0,1] [0,0] [0,2].

Definition SumSig : GenSig (stn 4) := four_rec [0,0] [0] [0] [0,1,1].

Definition IdSig : GenSig (stn 3) := three_rec [0,0,0] [] [0,0].

(* Define the signature of the eliminators for Fin by recursion *)
Definition FinSigElim (n : nat) : list nat.
Proof.
induction n as [|n ih].
- apply [0].
- apply (0 :: ih).
Defined.

(* Define the signature of the constructors for Fin by recursion *)
Definition FinSigConstructors (n : nat) : GenSig (stn n).
Proof.
intros [m p].
destruct (natlthorgeh m n) as [|h].
- apply [].
- induction (natgehtonegnatlth _ _ h p).
Defined.

(* The FinSig family is defined by recursion and decomposed into the
   type, the constructors and the eliminator *)
(* Definition FinSig (n : nat) : GenSig (unit ⨿ (stn n ⨿ unit)). *)
(* Proof. *)
(* induction 1 as [_|p]. *)
(* - apply []. *)
(* - induction p as [p|]. *)
(*   + apply (FinSigConstructors _ p). *)
(*   + apply (FinSigElim n). *)
(* Defined. *)

(* Uncurried version of the FinSig family *)
Definition FinSig : GenSig (Σ n, unit ⨿ (stn n ⨿ unit)).
Proof.
induction 1 as [n p].
induction p as [_|p].
- apply [].
- induction p as [p|].
  + apply (FinSigConstructors _ p).
  + apply (FinSigElim n).
Defined.

Lemma isdeceqFinSig : isdeceq (Σ n, unit ⨿ (stn n ⨿ unit)).
Proof.
intros [n p] [m q].
induction (isdeceqnat n m) as [h|h].
- induction h.
   + destruct (isdeceqcoprod isdecequnit
                (isdeceqcoprod (isdeceqstn n) isdecequnit) p q) as [Hpq|Hpq].
     * now rewrite Hpq; apply inl.
     * apply inr; intro H.
       assert (Hid : maponpaths pr1 H = idpath _).
       { apply isasetnat. }
       generalize (fiber_paths H); unfold base_paths.
       rewrite Hid, idpath_transportf; intro H'.
       apply (Hpq H').
- apply inr; intro H; apply (h (maponpaths pr1 H)).
Defined.

Definition NatSig : GenSig (stn 4) := four_rec [] [] [0] [0,0,2].

Definition WSig : GenSig (stn 3) := three_rec [0,1] [0,0] [0,3].

Definition USig : GenSig nat := fun _ => [].

Let SigHSET := Signature HSET has_homsets_HSET.

Definition MLTT79Sig :=
  (isdeceqstn 3,,PiSig) ++ (isdeceqstn 3,,SigmaSig) ++
  (isdeceqstn 4,,SumSig) ++ (isdeceqstn 3,,IdSig) ++
  (isdeceqFinSig,,FinSig) ++ (isdeceqstn 4,,NatSig) ++
  (isdeceqstn 3,,WSig) ++ (isdeceqnat,,USig).

Check MLTT79Sig.

Definition MLTT79Signature : SigHSET :=
  GenSigToSignature _ (pr1 MLTT79Sig) (pr2 MLTT79Sig).

Definition MLTT79Functor : functor HSET2 HSET2 :=
  Id_H _ _ CoproductsHSET MLTT79Signature.

Definition MLTT79Monad : Monad HSET :=
  GenSigToMonad _ (pr1 MLTT79Sig) (pr2 MLTT79Sig).

Lemma MLTT79Functor_Initial :
   Initial (FunctorAlg MLTT79Functor has_homsets_HSET2).
Proof.
apply (GenSigInitial _ (pr1 MLTT79Sig) (pr2 MLTT79Sig)).
Defined.

Definition MLTT79 : HSET2 :=
  alg_carrier _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_mor : HSET2⟦MLTT79Functor MLTT79,MLTT79⟧ :=
  alg_map _ (InitialObject MLTT79Functor_Initial).

Let MLTT79_alg : algebra_ob MLTT79Functor :=
  InitialObject MLTT79Functor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,MLTT79⟧ :=
  CoproductIn1 HSET2 _ ;; MLTT79_mor.


(* TODO: Adapt the rest *)

(* How to do this nicer? *)
(* Definition prod2 (x y : HSET2) : HSET2. *)
(* Proof. *)
(* apply ProductsHSET2; [apply x | apply y]. *)
(* Defined. *)

(* Definition app_map : HSET2⟦prod2 LC LC,LC⟧ := *)
(*   ArbitraryCoproductIn bool HSET2 _ true ;; CoproductIn2 HSET2 _ ;; LC_mor. *)

(* Definition app_map' (x : HSET) : HSET⟦(pr1 LC x × pr1 LC x)%set,pr1 LC x⟧. *)
(* Proof. *)
(* apply app_map. *)
(* Defined. *)

(* Let precomp_option X := (pre_composition_functor _ _ HSET has_homsets_HSET has_homsets_HSET *)
(*                   (option_functor HSET CoproductsHSET TerminalHSET) X). *)

(* Definition lam_map : HSET2⟦precomp_option LC,LC⟧ := *)
(*   ArbitraryCoproductIn bool HSET2 _ false ;; CoproductIn2 HSET2 _ ;; LC_mor. *)

(* Definition mk_lambdaAlgebra (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : algebra_ob MLTT79Functor. *)
(* Proof. *)
(* apply (tpair _ X). *)
(* simple refine (CoproductArrow _ _ fvar _). *)
(* simple refine (ArbitraryCoproductArrow _ _ _ _). *)
(* intro b; destruct b. *)
(* - apply fapp. *)
(* - apply flam. *)
(* Defined. *)

(* Definition foldr_map (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : *)
(*   algebra_mor MLTT79Functor LC_alg (mk_lambdaAlgebra X fvar fapp flam). *)
(* Proof. *)
(* apply (InitialArrow lambdaFunctor_Initial (mk_lambdaAlgebra X fvar fapp flam)). *)
(* Defined. *)

(* Definition foldr_map' (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : *)
(*    HSET2 ⟦ pr1 LC_alg, pr1 (mk_lambdaAlgebra X fvar fapp flam) ⟧. *)
(* Proof. *)
(* apply (foldr_map X fvar fapp flam). *)
(* Defined. *)

(* Lemma foldr_var (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : *)
(*   var_map ;; foldr_map X fvar fapp flam = fvar. *)
(* Proof. *)
(* assert (F := maponpaths (fun x => CoproductIn1 _ _ ;; x) *)
(*                         (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))). *)
(* rewrite assoc in F. *)
(* eapply pathscomp0; [apply F|]. *)
(* rewrite assoc. *)
(* eapply pathscomp0; [eapply cancel_postcomposition, CoproductOfArrowsIn1|]. *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; [eapply maponpaths, CoproductIn1Commutes|]. *)
(* apply id_left. *)
(* Defined. *)

(* Lemma foldr_app (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : *)
(*   app_map ;; foldr_map X fvar fapp flam = *)
(*   # (pr1 (Id * Id)) (foldr_map X fvar fapp flam) ;; fapp. *)
(* Proof. *)
(* assert (F := maponpaths (fun x => ArbitraryCoproductIn _ _ _ true ;; CoproductIn2 _ _ ;; x) *)
(*                         (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))). *)
(* rewrite assoc in F. *)
(* eapply pathscomp0; [apply F|]. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition. *)
(*   rewrite <- assoc. *)
(*   eapply maponpaths, CoproductOfArrowsIn2. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition, cancel_postcomposition. *)
(*   apply (ArbitraryCoproductOfArrowsIn _ _ (ArbitraryCoproducts_functor_precat _ _ _ *)
(*           (ArbitraryCoproducts_HSET _ (isasetifdeceq _ isdeceqbool)) *)
(*           _ (λ i, pr1 (Arity_to_Signature (MLTT79Sig i)) `LC_alg))). *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; [eapply maponpaths, CoproductIn2Commutes|]. *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; eapply maponpaths. *)
(*   refine (ArbitraryCoproductInCommutes _ _ _ _ _ _ true). *)
(* apply idpath. *)
(* Defined. *)

(* Lemma foldr_lam (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧) *)
(*   (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : *)
(*   lam_map ;; foldr_map X fvar fapp flam = *)
(*   # (pr1 (_ o option)) (foldr_map X fvar fapp flam) ;; flam. *)
(* Proof. *)
(* assert (F := maponpaths (fun x => ArbitraryCoproductIn _ _ _ false ;; CoproductIn2 _ _ ;; x) *)
(*                         (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))). *)
(* rewrite assoc in F. *)
(* eapply pathscomp0; [apply F|]. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition. *)
(*   rewrite <- assoc. *)
(*   eapply maponpaths, CoproductOfArrowsIn2. *)
(* rewrite assoc. *)
(* eapply pathscomp0. *)
(*   eapply cancel_postcomposition, cancel_postcomposition. *)
(*   apply (ArbitraryCoproductOfArrowsIn _ _ (ArbitraryCoproducts_functor_precat _ _ _ *)
(*           (ArbitraryCoproducts_HSET _ (isasetifdeceq _ isdeceqbool)) *)
(*           _ (λ i, pr1 (Arity_to_Signature (MLTT79Sig i)) `LC_alg))). *)
(* rewrite <- assoc. *)
(* eapply pathscomp0. *)
(*   eapply maponpaths, CoproductIn2Commutes. *)
(* rewrite <- assoc. *)
(* eapply pathscomp0; eapply maponpaths. *)
(*   refine (ArbitraryCoproductInCommutes _ _ _ _ _ _ false). *)
(* apply idpath. *)
(* Defined. *)

End MLTT79.
