Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339697_term_abbrevs.
Require Import TREAL_LE_TOTAL_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Lemma lem1339619 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339620 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_le x y) = (term0 x y).
Proof. exact (@lem1339619 x y). Qed.
Lemma lem1339621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1339622 (x : prod hreal hreal) (y : prod hreal hreal) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1339621) (@lem1339620 x y)). Qed.
Lemma lem1339624 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339625 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_le y x) = (term0 y x).
Proof. exact (@lem1339624 y x). Qed.
Lemma lem1339626 (y : prod hreal hreal) (x : prod hreal hreal) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1339622 x y) (@lem1339625 y x)). Qed.
Lemma lem1339629 (x : prod hreal hreal) : (term5 x) = (term6 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339626 y x)). Qed.
Lemma lem1339630 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339631 (x : prod hreal hreal) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1339630) (@lem1339629 x)). Qed.
Lemma lem1339637 (P : real -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339638 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (@lem1339637 (term13 x)). Qed.
Lemma lem1339639 (y : prod hreal hreal) (x : prod hreal hreal) : (term14 x y) = (term4 y x).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1339640 (x : prod hreal hreal) : (term15 x) = (term6 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339639 y x)). Qed.
Lemma lem1339641 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339642 (x : prod hreal hreal) : (term11 x) = (term8 x).
Proof. exact (MK_COMB (@lem1339641) (@lem1339640 x)). Qed.
Lemma lem1339643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339644 (x : prod hreal hreal) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1339643) (@lem1339642 x)). Qed.
Lemma lem1339645 (y : real) (x : prod hreal hreal) : (term18 x y) = (term19 y x).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1339646 (x : prod hreal hreal) : (term20 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1339645 y x)). Qed.
Lemma lem1339647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339648 (x : prod hreal hreal) : (term12 x) = (term21 x).
Proof. exact (MK_COMB (@lem1339647) (@lem1339646 x)). Qed.
Lemma lem1339649 (x : prod hreal hreal) : ((term11 x) = (term12 x)) = ((term8 x) = (term21 x)).
Proof. exact (MK_COMB (@lem1339644 x) (@lem1339648 x)). Qed.
Lemma lem1339650 (x : prod hreal hreal) : (term8 x) = (term21 x).
Proof. exact (EQ_MP (@lem1339649 x) (@lem1339638 x)). Qed.
Lemma lem1339659 (x : prod hreal hreal) : (term7 x) = (term21 x).
Proof. exact (TRANS (@lem1339631 x) (@lem1339650 x)). Qed.
Lemma lem1339660 : term22 = term23.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339659 x)). Qed.
Lemma lem1339661 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339662 : term24 = term25.
Proof. exact (MK_COMB (@lem1339661) (@lem1339660)). Qed.
Lemma lem1339668 (P : real -> Prop) : (term9 P) = (term10 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339669 : term26 = term27.
Proof. exact (@lem1339668 term28). Qed.
Lemma lem1339670 (x : prod hreal hreal) : (term29 x) = (term21 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1339671 : term30 = term23.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339670 x)). Qed.
Lemma lem1339672 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339673 : term26 = term25.
Proof. exact (MK_COMB (@lem1339672) (@lem1339671)). Qed.
Lemma lem1339674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339675 : term31 = term32.
Proof. exact (MK_COMB (@lem1339674) (@lem1339673)). Qed.
Lemma lem1339676 (x : real) : (term33 x) = (term34 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1339677 : term35 = term28.
Proof. exact (fun_ext (fun x : real => @lem1339676 x)). Qed.
Lemma lem1339678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339679 : term27 = term36.
Proof. exact (MK_COMB (@lem1339678) (@lem1339677)). Qed.
Lemma lem1339680 : (term26 = term27) = (term25 = term36).
Proof. exact (MK_COMB (@lem1339675) (@lem1339679)). Qed.
Lemma lem1339681 : term25 = term36.
Proof. exact (EQ_MP (@lem1339680) (@lem1339669)). Qed.
Lemma lem1339696 : term24 = term36.
Proof. exact (TRANS (@lem1339662) (@lem1339681)). Qed.
Lemma lem1339697 : term36.
Proof. exact (EQ_MP (@lem1339696) (@lem1330688)). Qed.
