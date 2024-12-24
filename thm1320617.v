Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320617_term_abbrevs.
Require Import NADD_MUL_SYM_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320534 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320535 (y : nadd) (x : nadd) : (term1 y x) = ((term2 x y) = (term2 y x)).
Proof. exact (@lem1320534 (nadd_mul x y) (nadd_mul y x)). Qed.
Lemma lem1320539 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320540 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320541 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1320540) (@lem1320539 x y)). Qed.
Lemma lem1320543 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320544 (y : nadd) (x : nadd) : (term2 y x) = (term3 y x).
Proof. exact (@lem1320543 y x). Qed.
Lemma lem1320545 (y : nadd) (x : nadd) : ((term2 x y) = (term2 y x)) = ((term3 x y) = (term3 y x)).
Proof. exact (MK_COMB (@lem1320541 x y) (@lem1320544 y x)). Qed.
Lemma lem1320548 (y : nadd) (x : nadd) : (term1 y x) = ((term3 x y) = (term3 y x)).
Proof. exact (TRANS (@lem1320535 y x) (@lem1320545 y x)). Qed.
Lemma lem1320549 (x : nadd) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320548 y x)). Qed.
Lemma lem1320550 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320551 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1320550) (@lem1320549 x)). Qed.
Lemma lem1320557 (P : hreal -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320558 (x : nadd) : (term12 x) = (term13 x).
Proof. exact (@lem1320557 (term14 x)). Qed.
Lemma lem1320559 (y : nadd) (x : nadd) : (term15 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1320560 (x : nadd) : (term16 x) = (term7 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320559 y x)). Qed.
Lemma lem1320561 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320562 (x : nadd) : (term12 x) = (term9 x).
Proof. exact (MK_COMB (@lem1320561) (@lem1320560 x)). Qed.
Lemma lem1320563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320564 (x : nadd) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1320563) (@lem1320562 x)). Qed.
Lemma lem1320565 (y : hreal) (x : nadd) : (term19 x y) = ((term20 x y) = (term21 y x)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1320566 (x : nadd) : (term22 x) = (term14 x).
Proof. exact (fun_ext (fun y : hreal => @lem1320565 y x)). Qed.
Lemma lem1320567 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320568 (x : nadd) : (term13 x) = (term23 x).
Proof. exact (MK_COMB (@lem1320567) (@lem1320566 x)). Qed.
Lemma lem1320569 (x : nadd) : ((term12 x) = (term13 x)) = ((term9 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1320564 x) (@lem1320568 x)). Qed.
Lemma lem1320570 (x : nadd) : (term9 x) = (term23 x).
Proof. exact (EQ_MP (@lem1320569 x) (@lem1320558 x)). Qed.
Lemma lem1320579 (x : nadd) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1320551 x) (@lem1320570 x)). Qed.
Lemma lem1320580 : term24 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1320579 x)). Qed.
Lemma lem1320581 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320582 : term26 = term27.
Proof. exact (MK_COMB (@lem1320581) (@lem1320580)). Qed.
Lemma lem1320588 (P : hreal -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320589 : term28 = term29.
Proof. exact (@lem1320588 term30). Qed.
Lemma lem1320590 (x : nadd) : (term31 x) = (term23 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1320591 : term32 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1320590 x)). Qed.
Lemma lem1320592 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320593 : term28 = term27.
Proof. exact (MK_COMB (@lem1320592) (@lem1320591)). Qed.
Lemma lem1320594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320595 : term33 = term34.
Proof. exact (MK_COMB (@lem1320594) (@lem1320593)). Qed.
Lemma lem1320596 (x : hreal) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1320597 : term37 = term30.
Proof. exact (fun_ext (fun x : hreal => @lem1320596 x)). Qed.
Lemma lem1320598 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320599 : term29 = term38.
Proof. exact (MK_COMB (@lem1320598) (@lem1320597)). Qed.
Lemma lem1320600 : (term28 = term29) = (term27 = term38).
Proof. exact (MK_COMB (@lem1320595) (@lem1320599)). Qed.
Lemma lem1320601 : term27 = term38.
Proof. exact (EQ_MP (@lem1320600) (@lem1320589)). Qed.
Lemma lem1320616 : term26 = term38.
Proof. exact (TRANS (@lem1320582) (@lem1320601)). Qed.
Lemma lem1320617 : term38.
Proof. exact (EQ_MP (@lem1320616) (@lem1278399)). Qed.
