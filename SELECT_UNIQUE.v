Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SELECT_UNIQUE_term_abbrevs.
Require Import ETA_AX_spec.
Require Import SELECT_REFL_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem9444 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : (term0 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem9445 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : t = (term0 A B t).
Proof. exact (SYM (@lem9444 A B t h1)). Qed.
Lemma lem9446 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : t = (term0 A B t).
Proof. exact (h1). Qed.
Lemma lem9447 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : (term0 A B t) = t.
Proof. exact (SYM (@lem9446 A B t h1)). Qed.
Lemma lem9448 {A B : Type'} (t : A -> B) : ((term0 A B t) = t) = (t = (term0 A B t)).
Proof. exact (prop_ext (fun h1 : (term0 A B t) = t => @lem9445 A B t h1) (fun h1 : t = (term0 A B t) => @lem9447 A B t h1)). Qed.
Lemma lem9449 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem9448 A B t)). Qed.
Lemma lem9450 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem9451 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem9450 A B) (@lem9449 A B)). Qed.
Lemma lem9452 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem9451 A B) (@lem9121 A B)). Qed.
Lemma lem9453 {A B : Type'} (t : A -> B) : term5 A B t.
Proof. exact (@lem9452 A B t). Qed.
Lemma lem9454 {A B : Type'} (t : A -> B) : (term5 A B t) = (t = (term0 A B t)).
Proof. exact (eq_refl (term5 A B t)). Qed.
Lemma lem9456 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : term6 A P x.
Proof. exact (h1). Qed.
Lemma lem9458 {A B : Type'} (t : A -> B) : t = (term0 A B t).
Proof. exact (EQ_MP (@lem9454 A B t) (@lem9453 A B t)). Qed.
Lemma lem9459 {A : Type'} (t : A -> Prop) : t = (term7 A t).
Proof. exact (@lem9458 A Prop t). Qed.
Lemma lem9460 {A : Type'} (P : A -> Prop) : P = (term7 A P).
Proof. exact (@lem9459 A P). Qed.
Lemma lem9461 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem9462 {A : Type'} (P : A -> Prop) : (@ε A P) = (term8 A P).
Proof. exact (MK_COMB (@lem9461 A) (@lem9460 A P)). Qed.
Lemma lem9463 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem9464 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem9463 A) (@lem9462 A P)). Qed.
Lemma lem9465 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem9466 {A : Type'} (P : A -> Prop) (x : A) : ((@ε A P) = x) = ((term8 A P) = x).
Proof. exact (MK_COMB (@lem9464 A P) (@lem9465 A x)). Qed.
Lemma lem9467 {A : Type'} (P : A -> Prop) (x : A) : ((term8 A P) = x) = ((@ε A P) = x).
Proof. exact (SYM (@lem9466 A P x)). Qed.
Lemma lem9468 {A : Type'} (x : A) : term11 A x.
Proof. exact (@lem9442 A x). Qed.
Lemma lem9469 {A : Type'} (x : A) : (term11 A x) = ((term12 A x) = x).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem9471 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term6 A P x) : term13 A P x y.
Proof. exact (@lem9456 A P x h1 y). Qed.
Lemma lem9472 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term13 A P x y) = ((P y) = (y = x)).
Proof. exact (eq_refl (term13 A P x y)). Qed.
Lemma lem9485 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term6 A P x) : (P y) = (y = x).
Proof. exact (EQ_MP (@lem9472 A P y x) (@lem9471 A y P x h1)). Qed.
Lemma lem9486 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term6 A P x) : (P y) = (y = x).
Proof. exact (@lem9485 A y P x h1). Qed.
Lemma lem9487 {A : Type'} (_385 : A) (P : A -> Prop) (x : A) (h1 : term6 A P x) : (P _385) = (_385 = x).
Proof. exact (@lem9486 A _385 P x h1). Qed.
Lemma lem9492 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term7 A P) = (term14 A x).
Proof. exact (fun_ext (fun _385 : A => @lem9487 A _385 P x h1)). Qed.
Lemma lem9493 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem9494 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term8 A P) = (term12 A x).
Proof. exact (MK_COMB (@lem9493 A) (@lem9492 A P x h1)). Qed.
Lemma lem9496 {A : Type'} (x : A) : (term12 A x) = x.
Proof. exact (EQ_MP (@lem9469 A x) (@lem9468 A x)). Qed.
Lemma lem9497 {A : Type'} (x : A) : (term12 A x) = x.
Proof. exact (@lem9496 A x). Qed.
Lemma lem9498 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term8 A P) = x.
Proof. exact (TRANS (@lem9494 A P x h1) (@lem9497 A x)). Qed.
Lemma lem9499 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem9500 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term10 A P) = (@eq A x).
Proof. exact (MK_COMB (@lem9499 A) (@lem9498 A P x h1)). Qed.
Lemma lem9501 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem9502 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : ((term8 A P) = x) = (x = x).
Proof. exact (MK_COMB (@lem9500 A P x h1) (@lem9501 A x)). Qed.
Lemma lem9504 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem9505 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem9504 A x). Qed.
Lemma lem9506 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : ((term8 A P) = x) = True.
Proof. exact (TRANS (@lem9502 A P x h1) (@lem9505 A x)). Qed.
Lemma lem9507 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : True = ((term8 A P) = x).
Proof. exact (SYM (@lem9506 A P x h1)). Qed.
Lemma lem9508 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term8 A P) = x.
Proof. exact (EQ_MP (@lem9507 A P x h1) (@lem0)). Qed.
Lemma lem9509 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (@ε A P) = x.
Proof. exact (EQ_MP (@lem9467 A P x) (@lem9508 A P x h1)). Qed.
Lemma lem9510 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (term6 A P x) = ((@ε A P) = x).
Proof. exact (prop_ext (fun h2 : term6 A P x => @lem9509 A P x h1) (fun h2 : (@ε A P) = x => @lem9456 A P x h1)). Qed.
Lemma lem9511 {A : Type'} (P : A -> Prop) (x : A) (h1 : term6 A P x) : (@ε A P) = x.
Proof. exact (EQ_MP (@lem9510 A P x h1) (@lem9456 A P x h1)). Qed.
Lemma lem9512 {A : Type'} (P : A -> Prop) (x : A) : term15 A P x.
Proof. exact (fun h0 : term6 A P x => @lem9511 A P x h0). Qed.
Lemma lem9517 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (fun x : A => @lem9512 A P x). Qed.
Lemma lem9522 {A : Type'} : term17 A.
Proof. exact (fun P : A -> Prop => @lem9517 A P). Qed.
