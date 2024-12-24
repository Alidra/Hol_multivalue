Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_ZERO_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm15249_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1648587 (x : real) : term0 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1648588 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1648590 (n : nat) : term3 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1648591 (n : nat) : (term3 n) = (term4 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1648592 (n : nat) : term4 n.
Proof. exact (EQ_MP (@lem1648591 n) (@lem1648590 n)). Qed.
Lemma lem1648593 (n : nat) : term5 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1648606 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1648607 (x : real) (n : nat) : term7 x n.
Proof. exact (@lem1648606 x n). Qed.
Lemma lem1648608 (x : real) (n : nat) : (term7 x n) = ((term8 x n) = (term9 x n)).
Proof. exact (eq_refl (term7 x n)). Qed.
Lemma lem1648612 (P : nat -> Prop) : term10 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1648613 : term11.
Proof. exact (@lem1648612 term12). Qed.
Lemma lem1648614 : term13 = (term14 = term15).
Proof. exact (eq_refl term13). Qed.
Lemma lem1648615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1648616 : term16 = term17.
Proof. exact (MK_COMB (@lem1648615) (@lem1648614)). Qed.
Lemma lem1648617 (n : nat) : (term18 n) = ((term19 n) = (term20 n)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem1648618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1648619 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem1648618) (@lem1648617 n)). Qed.
Lemma lem1648620 (n : nat) : (term23 n) = ((term24 n) = (term25 n)).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem1648621 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem1648619 n) (@lem1648620 n)). Qed.
Lemma lem1648622 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem1648621 n)). Qed.
Lemma lem1648623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1648624 : term30 = term31.
Proof. exact (MK_COMB (@lem1648623) (@lem1648622)). Qed.
Lemma lem1648625 : term32 = term33.
Proof. exact (MK_COMB (@lem1648616) (@lem1648624)). Qed.
Lemma lem1648626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1648627 : term34 = term35.
Proof. exact (MK_COMB (@lem1648626) (@lem1648625)). Qed.
Lemma lem1648628 (n : nat) : (term18 n) = ((term19 n) = (term20 n)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem1648629 : term36 = term12.
Proof. exact (fun_ext (fun n : nat => @lem1648628 n)). Qed.
Lemma lem1648630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1648631 : term37 = term38.
Proof. exact (MK_COMB (@lem1648630) (@lem1648629)). Qed.
Lemma lem1648632 : term11 = term39.
Proof. exact (MK_COMB (@lem1648627) (@lem1648631)). Qed.
Lemma lem1648633 : term39.
Proof. exact (EQ_MP (@lem1648632) (@lem1648613)). Qed.
Lemma lem1648638 (x : real) : (term40 x) = term41.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1648639 : term14 = term41.
Proof. exact (@lem1648638 term2). Qed.
Lemma lem1648640 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648641 : term42 = term43.
Proof. exact (MK_COMB (@lem1648640) (@lem1648639)). Qed.
Lemma lem1648643 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term44 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1648644 (x : nat) (z : real) (y : real) : (term45 x y z) = y.
Proof. exact (@lem1648643 real nat x z y). Qed.
Lemma lem1648645 : term15 = term41.
Proof. exact (@lem1648644 (NUMERAL 0) term2 term41). Qed.
Lemma lem1648646 : (term14 = term15) = (term41 = term41).
Proof. exact (MK_COMB (@lem1648641) (@lem1648645)). Qed.
Lemma lem1648648 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1648649 (x : real) : (x = x) = True.
Proof. exact (@lem1648648 real x). Qed.
Lemma lem1648650 : (term41 = term41) = True.
Proof. exact (@lem1648649 term41). Qed.
Lemma lem1648651 : (term14 = term15) = True.
Proof. exact (TRANS (@lem1648646) (@lem1648650)). Qed.
Lemma lem1648652 : True = (term14 = term15).
Proof. exact (SYM (@lem1648651)). Qed.
Lemma lem1648653 : term14 = term15.
Proof. exact (EQ_MP (@lem1648652) (@lem0)). Qed.
Lemma lem1648657 (x : real) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem1648608 x n) (@lem1648607 x n)). Qed.
Lemma lem1648658 (n : nat) : (term24 n) = (term46 n).
Proof. exact (@lem1648657 term2 n). Qed.
Lemma lem1648660 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1648588 x) (@lem1648587 x)). Qed.
Lemma lem1648661 (n : nat) : (term46 n) = term2.
Proof. exact (@lem1648660 (term19 n)). Qed.
Lemma lem1648662 (n : nat) : (term24 n) = term2.
Proof. exact (TRANS (@lem1648658 n) (@lem1648661 n)). Qed.
Lemma lem1648663 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648664 (n : nat) : (term47 n) = term48.
Proof. exact (MK_COMB (@lem1648663) (@lem1648662 n)). Qed.
Lemma lem1648668 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1648593 n (@lem1648592 n)). Qed.
Lemma lem1648669 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1648670 (n : nat) : (term49 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1648669) (@lem1648668 n)). Qed.
Lemma lem1648671 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1648672 (n : nat) : (term50 n) = term51.
Proof. exact (MK_COMB (@lem1648670 n) (@lem1648671)). Qed.
Lemma lem1648673 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1648674 (n : nat) : (term25 n) = term52.
Proof. exact (MK_COMB (@lem1648672 n) (@lem1648673)). Qed.
Lemma lem1648676 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1648677 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1648676 real t1 t2). Qed.
Lemma lem1648678 : term52 = term2.
Proof. exact (@lem1648677 term41 term2). Qed.
Lemma lem1648679 (n : nat) : (term25 n) = term2.
Proof. exact (TRANS (@lem1648674 n) (@lem1648678)). Qed.
Lemma lem1648680 (n : nat) : ((term24 n) = (term25 n)) = (term2 = term2).
Proof. exact (MK_COMB (@lem1648664 n) (@lem1648679 n)). Qed.
Lemma lem1648682 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1648683 (x : real) : (x = x) = True.
Proof. exact (@lem1648682 real x). Qed.
Lemma lem1648684 : (term2 = term2) = True.
Proof. exact (@lem1648683 term2). Qed.
Lemma lem1648685 (n : nat) : ((term24 n) = (term25 n)) = True.
Proof. exact (TRANS (@lem1648680 n) (@lem1648684)). Qed.
Lemma lem1648686 (n : nat) : True = ((term24 n) = (term25 n)).
Proof. exact (SYM (@lem1648685 n)). Qed.
Lemma lem1648687 (n : nat) : (term24 n) = (term25 n).
Proof. exact (EQ_MP (@lem1648686 n) (@lem0)). Qed.
Lemma lem1648688 (n : nat) : term27 n.
Proof. exact (fun h0 : (term19 n) = (term20 n) => @lem1648687 n). Qed.
Lemma lem1648693 : term31.
Proof. exact (fun n : nat => @lem1648688 n). Qed.
Lemma lem1648694 : term33.
Proof. exact (conj (@lem1648653) (@lem1648693)). Qed.
Lemma lem1648695 : term38.
Proof. exact (@lem1648633 (@lem1648694)). Qed.
