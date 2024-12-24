Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_CONS_NIL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1073523_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm82_spec.
Lemma lem1111470 {A : Type'} (a0' : A) : term0 A a0'.
Proof. exact (@lem1073523 A a0'). Qed.
Lemma lem1111471 {A : Type'} (a0' : A) : (term0 A a0') = (term1 A a0').
Proof. exact (eq_refl (term0 A a0')). Qed.
Lemma lem1111472 {A : Type'} (a0' : A) : term1 A a0'.
Proof. exact (EQ_MP (@lem1111471 A a0') (@lem1111470 A a0')). Qed.
Lemma lem1111473 {A : Type'} (a0' : A) (a1' : list A) : term2 A a0' a1'.
Proof. exact (@lem1111472 A a0' a1'). Qed.
Lemma lem1111474 {A : Type'} (a0' : A) (a1' : list A) : (term2 A a0' a1') = (term3 A a0' a1').
Proof. exact (eq_refl (term2 A a0' a1')). Qed.
Lemma lem1111475 {A : Type'} (a0' : A) (a1' : list A) : term3 A a0' a1'.
Proof. exact (EQ_MP (@lem1111474 A a0' a1') (@lem1111473 A a0' a1')). Qed.
Lemma lem1111479 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (@nil A) = (@cons A a0' a1').
Proof. exact (h1). Qed.
Lemma lem1111480 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (@cons A a0' a1') = (@nil A).
Proof. exact (SYM (@lem1111479 A a0' a1' h1)). Qed.
Lemma lem1111481 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@cons A a0' a1') = (@nil A)) : (@cons A a0' a1') = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1111482 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@cons A a0' a1') = (@nil A)) : (@nil A) = (@cons A a0' a1').
Proof. exact (SYM (@lem1111481 A a0' a1' h1)). Qed.
Lemma lem1111483 {A : Type'} (a0' : A) (a1' : list A) : ((@nil A) = (@cons A a0' a1')) = ((@cons A a0' a1') = (@nil A)).
Proof. exact (prop_ext (fun h1 : (@nil A) = (@cons A a0' a1') => @lem1111480 A a0' a1' h1) (fun h1 : (@cons A a0' a1') = (@nil A) => @lem1111482 A a0' a1' h1)). Qed.
Lemma lem1111484 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1111485 {A : Type'} (a0' : A) (a1' : list A) : (term3 A a0' a1') = (term4 A a0' a1').
Proof. exact (MK_COMB (@lem1111484) (@lem1111483 A a0' a1')). Qed.
Lemma lem1111486 {A : Type'} (a0' : A) (a1' : list A) : term4 A a0' a1'.
Proof. exact (EQ_MP (@lem1111485 A a0' a1') (@lem1111475 A a0' a1')). Qed.
Lemma lem1111487 {A : Type'} (a0' : A) (a1' : list A) : term5 A a0' a1'.
Proof. exact (@lem82 ((@cons A a0' a1') = (@nil A))). Qed.
Lemma lem1111498 {A : Type'} (a0' : A) (a1' : list A) : ((@cons A a0' a1') = (@nil A)) = False.
Proof. exact (@lem1111487 A a0' a1' (@lem1111486 A a0' a1')). Qed.
Lemma lem1111499 {A : Type'} (a0' : A) (a1' : list A) : ((@cons A a0' a1') = (@nil A)) = False.
Proof. exact (@lem1111498 A a0' a1'). Qed.
Lemma lem1111500 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1111499 A h t). Qed.
Lemma lem1111501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1111502 {A : Type'} (h : A) (t : list A) : (term4 A h t) = (~ False).
Proof. exact (MK_COMB (@lem1111501) (@lem1111500 A h t)). Qed.
Lemma lem1111504 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1111505 {A : Type'} (h : A) (t : list A) : (term4 A h t) = True.
Proof. exact (TRANS (@lem1111502 A h t) (@lem1111504)). Qed.
Lemma lem1111506 {A : Type'} (h : A) : (term6 A h) = (term7 A).
Proof. exact (fun_ext (fun t : list A => @lem1111505 A h t)). Qed.
Lemma lem1111507 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111508 {A : Type'} (h : A) : (term8 A h) = (term9 A).
Proof. exact (MK_COMB (@lem1111507 A) (@lem1111506 A h)). Qed.
Lemma lem1111510 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111511 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem1111510 (list A) t). Qed.
Lemma lem1111512 {A : Type'} : (term9 A) = True.
Proof. exact (@lem1111511 A True). Qed.
Lemma lem1111513 {A : Type'} (h : A) : (term8 A h) = True.
Proof. exact (TRANS (@lem1111508 A h) (@lem1111512 A)). Qed.
Lemma lem1111514 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun h : A => @lem1111513 A h)). Qed.
Lemma lem1111515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1111516 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem1111515 A) (@lem1111514 A)). Qed.
Lemma lem1111518 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111519 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (@lem1111518 A t). Qed.
Lemma lem1111520 {A : Type'} : (term15 A) = True.
Proof. exact (@lem1111519 A True). Qed.
Lemma lem1111521 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem1111516 A) (@lem1111520 A)). Qed.
Lemma lem1111522 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem1111521 A)). Qed.
Lemma lem1111523 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem1111522 A) (@lem0)). Qed.
