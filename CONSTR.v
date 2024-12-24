Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONSTR_term_abbrevs.
Lemma lem1059524 {A : Type'} : (@CONSTR A) = (term0 A).
Proof. exact (@CONSTR_def A). Qed.
Lemma lem1059525 (_17428 : nat) : _17428 = _17428.
Proof. exact (eq_refl _17428). Qed.
Lemma lem1059526 {A : Type'} (_17428 : nat) : (@CONSTR A _17428) = (term1 A _17428).
Proof. exact (MK_COMB (@lem1059524 A) (@lem1059525 _17428)). Qed.
Lemma lem1059527 {A : Type'} (_17428 : nat) : (term1 A _17428) = (term2 A _17428).
Proof. exact (eq_refl (term1 A _17428)). Qed.
Lemma lem1059528 {A : Type'} (_17428 : nat) : (@CONSTR A _17428) = (term2 A _17428).
Proof. exact (TRANS (@lem1059526 A _17428) (@lem1059527 A _17428)). Qed.
Lemma lem1059529 {A : Type'} (_17429 : A) : _17429 = _17429.
Proof. exact (eq_refl _17429). Qed.
Lemma lem1059530 {A : Type'} (_17428 : nat) (_17429 : A) : (@CONSTR A _17428 _17429) = (term3 A _17428 _17429).
Proof. exact (MK_COMB (@lem1059528 A _17428) (@lem1059529 A _17429)). Qed.
Lemma lem1059531 {A : Type'} (_17428 : nat) (_17429 : A) : (term3 A _17428 _17429) = (term4 A _17428 _17429).
Proof. exact (eq_refl (term3 A _17428 _17429)). Qed.
Lemma lem1059532 {A : Type'} (_17428 : nat) (_17429 : A) : (@CONSTR A _17428 _17429) = (term4 A _17428 _17429).
Proof. exact (TRANS (@lem1059530 A _17428 _17429) (@lem1059531 A _17428 _17429)). Qed.
Lemma lem1059533 {A : Type'} (_17430 : type1614 A) : _17430 = _17430.
Proof. exact (eq_refl _17430). Qed.
Lemma lem1059534 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : (@CONSTR A _17428 _17429 _17430) = (term5 A _17428 _17429 _17430).
Proof. exact (MK_COMB (@lem1059532 A _17428 _17429) (@lem1059533 A _17430)). Qed.
Lemma lem1059535 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : (term5 A _17428 _17429 _17430) = (term6 A _17428 _17429 _17430).
Proof. exact (eq_refl (term5 A _17428 _17429 _17430)). Qed.
Lemma lem1059536 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : (@CONSTR A _17428 _17429 _17430) = (term6 A _17428 _17429 _17430).
Proof. exact (TRANS (@lem1059534 A _17428 _17429 _17430) (@lem1059535 A _17428 _17429 _17430)). Qed.
Lemma lem1059537 {A : Type'} (_17428 : nat) (_17429 : A) : term7 A _17428 _17429.
Proof. exact (fun _17430 : type1614 A => @lem1059536 A _17428 _17429 _17430). Qed.
Lemma lem1059538 {A : Type'} (_17428 : nat) : term8 A _17428.
Proof. exact (fun _17429 : A => @lem1059537 A _17428 _17429). Qed.
Lemma lem1059539 {A : Type'} : term9 A.
Proof. exact (fun _17428 : nat => @lem1059538 A _17428). Qed.
Lemma lem1059540 {A : Type'} (_17428 : nat) : term10 A _17428.
Proof. exact (@lem1059539 A _17428). Qed.
Lemma lem1059541 {A : Type'} (_17428 : nat) : (term10 A _17428) = (term8 A _17428).
Proof. exact (eq_refl (term10 A _17428)). Qed.
Lemma lem1059542 {A : Type'} (_17428 : nat) : term8 A _17428.
Proof. exact (EQ_MP (@lem1059541 A _17428) (@lem1059540 A _17428)). Qed.
Lemma lem1059543 {A : Type'} (_17428 : nat) (_17429 : A) : term11 A _17428 _17429.
Proof. exact (@lem1059542 A _17428 _17429). Qed.
Lemma lem1059544 {A : Type'} (_17428 : nat) (_17429 : A) : (term11 A _17428 _17429) = (term7 A _17428 _17429).
Proof. exact (eq_refl (term11 A _17428 _17429)). Qed.
Lemma lem1059545 {A : Type'} (_17428 : nat) (_17429 : A) : term7 A _17428 _17429.
Proof. exact (EQ_MP (@lem1059544 A _17428 _17429) (@lem1059543 A _17428 _17429)). Qed.
Lemma lem1059546 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : term12 A _17428 _17429 _17430.
Proof. exact (@lem1059545 A _17428 _17429 _17430). Qed.
Lemma lem1059547 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : (term12 A _17428 _17429 _17430) = ((@CONSTR A _17428 _17429 _17430) = (term6 A _17428 _17429 _17430)).
Proof. exact (eq_refl (term12 A _17428 _17429 _17430)). Qed.
Lemma lem1059548 {A : Type'} (_17428 : nat) (_17429 : A) (_17430 : type1614 A) : (@CONSTR A _17428 _17429 _17430) = (term6 A _17428 _17429 _17430).
Proof. exact (EQ_MP (@lem1059547 A _17428 _17429 _17430) (@lem1059546 A _17428 _17429 _17430)). Qed.
Lemma lem1059604 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term6 A c i r).
Proof. exact (@lem1059548 A c i r). Qed.
Lemma lem1059605 {A : Type'} (c : nat) (i : A) : term7 A c i.
Proof. exact (fun r : type1614 A => @lem1059604 A c i r). Qed.
Lemma lem1059606 {A : Type'} (c : nat) : term8 A c.
Proof. exact (fun i : A => @lem1059605 A c i). Qed.
Lemma lem1059607 {A : Type'} : term9 A.
Proof. exact (fun c : nat => @lem1059606 A c). Qed.
