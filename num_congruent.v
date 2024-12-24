Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_congruent_term_abbrevs.
Require Import cong_spec.
Require Import num_mod_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2837525 (n : nat) : term0 n.
Proof. exact (@lem2837524 n). Qed.
Lemma lem2837526 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2837527 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2837526 n) (@lem2837525 n)). Qed.
Lemma lem2837528 (n : nat) (x : nat) : term2 n x.
Proof. exact (@lem2837527 n x). Qed.
Lemma lem2837529 (n : nat) (x : nat) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2837530 (n : nat) (x : nat) : term3 n x.
Proof. exact (EQ_MP (@lem2837529 n x) (@lem2837528 n x)). Qed.
Lemma lem2837531 (n : nat) (x : nat) (y : nat) : term4 n x y.
Proof. exact (@lem2837530 n x y). Qed.
Lemma lem2837532 (n : nat) (x : nat) (y : nat) : (term4 n x y) = ((num_mod n x y) = (term5 n x y)).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2837534 {A : Type'} (rel : type1402 A) : term6 A rel.
Proof. exact (@lem2427819 A rel). Qed.
Lemma lem2837535 {A : Type'} (rel : type1402 A) : (term6 A rel) = (term7 A rel).
Proof. exact (eq_refl (term6 A rel)). Qed.
Lemma lem2837536 {A : Type'} (rel : type1402 A) : term7 A rel.
Proof. exact (EQ_MP (@lem2837535 A rel) (@lem2837534 A rel)). Qed.
Lemma lem2837537 {A : Type'} (rel : type1402 A) (x : A) : term8 A rel x.
Proof. exact (@lem2837536 A rel x). Qed.
Lemma lem2837538 {A : Type'} (rel : type1402 A) (x : A) : (term8 A rel x) = (term9 A rel x).
Proof. exact (eq_refl (term8 A rel x)). Qed.
Lemma lem2837539 {A : Type'} (rel : type1402 A) (x : A) : term9 A rel x.
Proof. exact (EQ_MP (@lem2837538 A rel x) (@lem2837537 A rel x)). Qed.
Lemma lem2837540 {A : Type'} (rel : type1402 A) (x : A) (y : A) : term10 A rel x y.
Proof. exact (@lem2837539 A rel x y). Qed.
Lemma lem2837541 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (term10 A rel x y) = ((@eq2 A x y rel) = (rel x y)).
Proof. exact (eq_refl (term10 A rel x y)). Qed.
Lemma lem2837558 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (@eq2 A x y rel) = (rel x y).
Proof. exact (EQ_MP (@lem2837541 A rel x y) (@lem2837540 A rel x y)). Qed.
Lemma lem2837559 (rel : type1605) (x : nat) (y : nat) : (@eq2 nat x y rel) = (rel x y).
Proof. exact (@lem2837558 nat rel x y). Qed.
Lemma lem2837560 (n : nat) (x : nat) (y : nat) : (term11 x y n) = (num_mod n x y).
Proof. exact (@lem2837559 (num_mod n) x y). Qed.
Lemma lem2837562 (n : nat) (x : nat) (y : nat) : (num_mod n x y) = (term5 n x y).
Proof. exact (EQ_MP (@lem2837532 n x y) (@lem2837531 n x y)). Qed.
Lemma lem2837563 (n : nat) (x : nat) (y : nat) : (term11 x y n) = (term5 n x y).
Proof. exact (TRANS (@lem2837560 n x y) (@lem2837562 n x y)). Qed.
Lemma lem2837564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2837565 (n : nat) (x : nat) (y : nat) : (term12 x y n) = (term13 n x y).
Proof. exact (MK_COMB (@lem2837564) (@lem2837563 n x y)). Qed.
Lemma lem2837567 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (@eq2 A x y rel) = (rel x y).
Proof. exact (EQ_MP (@lem2837541 A rel x y) (@lem2837540 A rel x y)). Qed.
Lemma lem2837568 (rel : type1550) (x : int) (y : int) : (@eq2 int x y rel) = (rel x y).
Proof. exact (@lem2837567 int rel x y). Qed.
Lemma lem2837569 (n : nat) (x : nat) (y : nat) : (term14 x y n) = (term5 n x y).
Proof. exact (@lem2837568 (term15 n) (int_of_num x) (int_of_num y)). Qed.
Lemma lem2837570 (n : nat) (x : nat) (y : nat) : ((term11 x y n) = (term14 x y n)) = ((term5 n x y) = (term5 n x y)).
Proof. exact (MK_COMB (@lem2837565 n x y) (@lem2837569 n x y)). Qed.
Lemma lem2837572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2837573 (x : Prop) : (x = x) = True.
Proof. exact (@lem2837572 Prop x). Qed.
Lemma lem2837574 (n : nat) (x : nat) (y : nat) : ((term5 n x y) = (term5 n x y)) = True.
Proof. exact (@lem2837573 (term5 n x y)). Qed.
Lemma lem2837575 (x : nat) (y : nat) (n : nat) : ((term11 x y n) = (term14 x y n)) = True.
Proof. exact (TRANS (@lem2837570 n x y) (@lem2837574 n x y)). Qed.
Lemma lem2837576 (x : nat) (y : nat) : (term16 x y) = term17.
Proof. exact (fun_ext (fun n : nat => @lem2837575 x y n)). Qed.
Lemma lem2837577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2837578 (x : nat) (y : nat) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem2837577) (@lem2837576 x y)). Qed.
Lemma lem2837580 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2837581 (t : Prop) : (term21 t) = t.
Proof. exact (@lem2837580 nat t). Qed.
Lemma lem2837582 : term19 = True.
Proof. exact (@lem2837581 True). Qed.
Lemma lem2837583 (x : nat) (y : nat) : (term18 x y) = True.
Proof. exact (TRANS (@lem2837578 x y) (@lem2837582)). Qed.
Lemma lem2837584 (x : nat) : (term22 x) = term17.
Proof. exact (fun_ext (fun y : nat => @lem2837583 x y)). Qed.
Lemma lem2837585 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2837586 (x : nat) : (term23 x) = term19.
Proof. exact (MK_COMB (@lem2837585) (@lem2837584 x)). Qed.
Lemma lem2837588 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2837589 (t : Prop) : (term21 t) = t.
Proof. exact (@lem2837588 nat t). Qed.
Lemma lem2837590 : term19 = True.
Proof. exact (@lem2837589 True). Qed.
Lemma lem2837591 (x : nat) : (term23 x) = True.
Proof. exact (TRANS (@lem2837586 x) (@lem2837590)). Qed.
Lemma lem2837592 : term24 = term17.
Proof. exact (fun_ext (fun x : nat => @lem2837591 x)). Qed.
Lemma lem2837593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2837594 : term25 = term19.
Proof. exact (MK_COMB (@lem2837593) (@lem2837592)). Qed.
Lemma lem2837596 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2837597 (t : Prop) : (term21 t) = t.
Proof. exact (@lem2837596 nat t). Qed.
Lemma lem2837598 : term19 = True.
Proof. exact (@lem2837597 True). Qed.
Lemma lem2837599 : term25 = True.
Proof. exact (TRANS (@lem2837594) (@lem2837598)). Qed.
Lemma lem2837600 : True = term25.
Proof. exact (SYM (@lem2837599)). Qed.
Lemma lem2837601 : term25.
Proof. exact (EQ_MP (@lem2837600) (@lem0)). Qed.
