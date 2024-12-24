Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LID_term_abbrevs.
Require Import ETA_AX_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_mul_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1278499 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem1278500 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem1278501 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem1278500 A B t) (@lem1278499 A B t)). Qed.
Lemma lem1278502 (x : nadd) : term2 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1278503 (x : nadd) : (term2 x) = (nadd_eq x x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1278504 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1278503 x) (@lem1278502 x)). Qed.
Lemma lem1278505 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1278507 : term3.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1278508 : term4.
Proof. exact (proj2 (@lem1278507)). Qed.
Lemma lem1278529 : term5.
Proof. exact (proj1 (@lem1278508)). Qed.
Lemma lem1278530 (n : nat) : term6 n.
Proof. exact (@lem1278529 n). Qed.
Lemma lem1278531 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1278541 (x : nadd) : term8 x.
Proof. exact (@lem1276766 x). Qed.
Lemma lem1278542 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1278543 (x : nadd) : term9 x.
Proof. exact (EQ_MP (@lem1278542 x) (@lem1278541 x)). Qed.
Lemma lem1278544 (x : nadd) (y : nadd) : term10 x y.
Proof. exact (@lem1278543 x y). Qed.
Lemma lem1278545 (x : nadd) (y : nadd) : (term10 x y) = ((nadd_mul x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1278547 (k : nat) : term12 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1278548 (k : nat) : (term12 k) = ((term13 k) = (term14 k)).
Proof. exact (eq_refl (term12 k)). Qed.
Lemma lem1278555 (x : nadd) (y : nadd) : (nadd_mul x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1278545 x y) (@lem1278544 x y)). Qed.
Lemma lem1278556 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (@lem1278555 term17 x). Qed.
Lemma lem1278558 (k : nat) : (term13 k) = (term14 k).
Proof. exact (EQ_MP (@lem1278548 k) (@lem1278547 k)). Qed.
Lemma lem1278559 : term18 = term19.
Proof. exact (@lem1278558 term20). Qed.
Lemma lem1278561 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem1278531 n) (@lem1278530 n)). Qed.
Lemma lem1278562 : term19 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1278561 n)). Qed.
Lemma lem1278563 : term18 = term21.
Proof. exact (TRANS (@lem1278559) (@lem1278562)). Qed.
Lemma lem1278564 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1278565 (x : nadd) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem1278563) (@lem1278564 x n)). Qed.
Lemma lem1278567 {A B : Type'} (f : A -> B) (y : A) : (term24 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278568 (f : nat -> nat) (y : nat) : (term25 f y) = (f y).
Proof. exact (@lem1278567 nat nat f y). Qed.
Lemma lem1278569 (x : nadd) (n : nat) : (term26 x n) = (term23 x n).
Proof. exact (@lem1278568 term21 (dest_nadd x n)). Qed.
Lemma lem1278570 (n : nat) : (term27 n) = n.
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem1278571 : term28 = term21.
Proof. exact (fun_ext (fun n : nat => @lem1278570 n)). Qed.
Lemma lem1278572 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1278573 (x : nadd) (n : nat) : (term26 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem1278571) (@lem1278572 x n)). Qed.
Lemma lem1278574 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278575 (x : nadd) (n : nat) : (term29 x n) = (term30 x n).
Proof. exact (MK_COMB (@lem1278574) (@lem1278573 x n)). Qed.
Lemma lem1278576 (x : nadd) (n : nat) : (term23 x n) = (dest_nadd x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1278577 (x : nadd) (n : nat) : ((term26 x n) = (term23 x n)) = ((term23 x n) = (dest_nadd x n)).
Proof. exact (MK_COMB (@lem1278575 x n) (@lem1278576 x n)). Qed.
Lemma lem1278578 (x : nadd) (n : nat) : (term23 x n) = (dest_nadd x n).
Proof. exact (EQ_MP (@lem1278577 x n) (@lem1278569 x n)). Qed.
Lemma lem1278579 (x : nadd) (n : nat) : (term22 x n) = (dest_nadd x n).
Proof. exact (TRANS (@lem1278565 x n) (@lem1278578 x n)). Qed.
Lemma lem1278580 (x : nadd) : (term31 x) = (term32 x).
Proof. exact (fun_ext (fun n : nat => @lem1278579 x n)). Qed.
Lemma lem1278581 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1278582 (x : nadd) : (term16 x) = (term33 x).
Proof. exact (MK_COMB (@lem1278581) (@lem1278580 x)). Qed.
Lemma lem1278583 (x : nadd) : (term15 x) = (term33 x).
Proof. exact (TRANS (@lem1278556 x) (@lem1278582 x)). Qed.
Lemma lem1278584 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1278585 (x : nadd) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1278584) (@lem1278583 x)). Qed.
Lemma lem1278586 (x : nadd) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1278587 (x : nadd) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1278585 x) (@lem1278586 x)). Qed.
Lemma lem1278588 : term38 = term39.
Proof. exact (fun_ext (fun x : nadd => @lem1278587 x)). Qed.
Lemma lem1278589 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1278590 : term40 = term41.
Proof. exact (MK_COMB (@lem1278589) (@lem1278588)). Qed.
Lemma lem1278595 : term41 = term40.
Proof. exact (SYM (@lem1278590)). Qed.
Lemma lem1278602 (t : nat -> nat) : (term42 t) = t.
Proof. exact (@lem1278501 nat nat t). Qed.
Lemma lem1278603 (x : nadd) : (term32 x) = (dest_nadd x).
Proof. exact (@lem1278602 (dest_nadd x)). Qed.
Lemma lem1278604 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1278605 (x : nadd) : (term33 x) = (term43 x).
Proof. exact (MK_COMB (@lem1278604) (@lem1278603 x)). Qed.
Lemma lem1278607 (a : nadd) : (term43 a) = a.
Proof. exact (@axiom_19 a). Qed.
Lemma lem1278608 (x : nadd) : (term43 x) = x.
Proof. exact (@lem1278607 x). Qed.
Lemma lem1278609 (x : nadd) : (term33 x) = x.
Proof. exact (TRANS (@lem1278605 x) (@lem1278608 x)). Qed.
Lemma lem1278610 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1278611 (x : nadd) : (term35 x) = (nadd_eq x).
Proof. exact (MK_COMB (@lem1278610) (@lem1278609 x)). Qed.
Lemma lem1278612 (x : nadd) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1278613 (x : nadd) : (term37 x) = (nadd_eq x x).
Proof. exact (MK_COMB (@lem1278611 x) (@lem1278612 x)). Qed.
Lemma lem1278615 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1278505 x) (@lem1278504 x)). Qed.
Lemma lem1278616 (x : nadd) : (term37 x) = True.
Proof. exact (TRANS (@lem1278613 x) (@lem1278615 x)). Qed.
Lemma lem1278617 : term39 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1278616 x)). Qed.
Lemma lem1278618 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1278619 : term41 = term45.
Proof. exact (MK_COMB (@lem1278618) (@lem1278617)). Qed.
Lemma lem1278621 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1278622 (t : Prop) : (term47 t) = t.
Proof. exact (@lem1278621 nadd t). Qed.
Lemma lem1278623 : term45 = True.
Proof. exact (@lem1278622 True). Qed.
Lemma lem1278624 : term41 = True.
Proof. exact (TRANS (@lem1278619) (@lem1278623)). Qed.
Lemma lem1278625 : True = term41.
Proof. exact (SYM (@lem1278624)). Qed.
Lemma lem1278626 : term41.
Proof. exact (EQ_MP (@lem1278625) (@lem0)). Qed.
Lemma lem1278627 : term40.
Proof. exact (EQ_MP (@lem1278595) (@lem1278626)). Qed.
