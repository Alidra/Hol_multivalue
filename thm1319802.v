Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1319802_term_abbrevs.
Require Import NADD_LE_EXISTS_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm1318755_spec.
Require Import thm1318756_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1319649 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1319651 (x : nadd) (y : nadd) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1319650) (@lem1319649 x y)). Qed.
Lemma lem1319672 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term3 x) = (term3 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1319673 (y : nadd) (x : nadd) (d : nadd) : (term4 y x d) = ((term3 y) = (term5 x d)).
Proof. exact (@lem1319672 y (nadd_add x d)). Qed.
Lemma lem1319677 (x : nadd) (y : nadd) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1319678 (x : nadd) (d : nadd) : (term5 x d) = (term6 x d).
Proof. exact (@lem1319677 x d). Qed.
Lemma lem1319679 (y : nadd) : (term7 y) = (term7 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem1319680 (y : nadd) (x : nadd) (d : nadd) : ((term3 y) = (term5 x d)) = ((term3 y) = (term6 x d)).
Proof. exact (MK_COMB (@lem1319679 y) (@lem1319678 x d)). Qed.
Lemma lem1319683 (y : nadd) (x : nadd) (d : nadd) : (term4 y x d) = ((term3 y) = (term6 x d)).
Proof. exact (TRANS (@lem1319673 y x d) (@lem1319680 y x d)). Qed.
Lemma lem1319684 (y : nadd) (x : nadd) : (term8 y x) = (term9 y x).
Proof. exact (fun_ext (fun d : nadd => @lem1319683 y x d)). Qed.
Lemma lem1319685 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1319686 (y : nadd) (x : nadd) : (term10 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1319685) (@lem1319684 y x)). Qed.
Lemma lem1319692 (P : hreal -> Prop) : (term12 P) = (term13 P).
Proof. exact (EQ_MP (@lem1318756 P) (@lem1318755 P)). Qed.
Lemma lem1319693 (y : nadd) (x : nadd) : (term14 y x) = (term15 y x).
Proof. exact (@lem1319692 (term16 y x)). Qed.
Lemma lem1319694 (y : nadd) (x : nadd) (d : nadd) : (term17 y x d) = ((term3 y) = (term6 x d)).
Proof. exact (eq_refl (term17 y x d)). Qed.
Lemma lem1319695 (y : nadd) (x : nadd) : (term18 y x) = (term9 y x).
Proof. exact (fun_ext (fun d : nadd => @lem1319694 y x d)). Qed.
Lemma lem1319696 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1319697 (y : nadd) (x : nadd) : (term14 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1319696) (@lem1319695 y x)). Qed.
Lemma lem1319698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319699 (y : nadd) (x : nadd) : (term19 y x) = (term20 y x).
Proof. exact (MK_COMB (@lem1319698) (@lem1319697 y x)). Qed.
Lemma lem1319700 (y : nadd) (x : nadd) (d : hreal) : (term21 y x d) = ((term3 y) = (term22 x d)).
Proof. exact (eq_refl (term21 y x d)). Qed.
Lemma lem1319701 (y : nadd) (x : nadd) : (term23 y x) = (term16 y x).
Proof. exact (fun_ext (fun d : hreal => @lem1319700 y x d)). Qed.
Lemma lem1319702 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1319703 (y : nadd) (x : nadd) : (term15 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1319702) (@lem1319701 y x)). Qed.
Lemma lem1319704 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term11 y x) = (term24 y x)).
Proof. exact (MK_COMB (@lem1319699 y x) (@lem1319703 y x)). Qed.
Lemma lem1319705 (y : nadd) (x : nadd) : (term11 y x) = (term24 y x).
Proof. exact (EQ_MP (@lem1319704 y x) (@lem1319693 y x)). Qed.
Lemma lem1319714 (y : nadd) (x : nadd) : (term10 y x) = (term24 y x).
Proof. exact (TRANS (@lem1319686 y x) (@lem1319705 y x)). Qed.
Lemma lem1319715 (y : nadd) (x : nadd) : (term25 y x) = (term26 y x).
Proof. exact (MK_COMB (@lem1319651 x y) (@lem1319714 y x)). Qed.
Lemma lem1319718 (x : nadd) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319715 y x)). Qed.
Lemma lem1319719 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319720 (x : nadd) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1319719) (@lem1319718 x)). Qed.
Lemma lem1319726 (P : hreal -> Prop) : (term31 P) = (term32 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319727 (x : nadd) : (term33 x) = (term34 x).
Proof. exact (@lem1319726 (term35 x)). Qed.
Lemma lem1319728 (y : nadd) (x : nadd) : (term36 x y) = (term26 y x).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1319729 (x : nadd) : (term37 x) = (term28 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319728 y x)). Qed.
Lemma lem1319730 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319731 (x : nadd) : (term33 x) = (term30 x).
Proof. exact (MK_COMB (@lem1319730) (@lem1319729 x)). Qed.
Lemma lem1319732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319733 (x : nadd) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1319732) (@lem1319731 x)). Qed.
Lemma lem1319734 (y : hreal) (x : nadd) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1319735 (x : nadd) : (term42 x) = (term35 x).
Proof. exact (fun_ext (fun y : hreal => @lem1319734 y x)). Qed.
Lemma lem1319736 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319737 (x : nadd) : (term34 x) = (term43 x).
Proof. exact (MK_COMB (@lem1319736) (@lem1319735 x)). Qed.
Lemma lem1319738 (x : nadd) : ((term33 x) = (term34 x)) = ((term30 x) = (term43 x)).
Proof. exact (MK_COMB (@lem1319733 x) (@lem1319737 x)). Qed.
Lemma lem1319739 (x : nadd) : (term30 x) = (term43 x).
Proof. exact (EQ_MP (@lem1319738 x) (@lem1319727 x)). Qed.
Lemma lem1319756 (x : nadd) : (term29 x) = (term43 x).
Proof. exact (TRANS (@lem1319720 x) (@lem1319739 x)). Qed.
Lemma lem1319757 : term44 = term45.
Proof. exact (fun_ext (fun x : nadd => @lem1319756 x)). Qed.
Lemma lem1319758 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319759 : term46 = term47.
Proof. exact (MK_COMB (@lem1319758) (@lem1319757)). Qed.
Lemma lem1319765 (P : hreal -> Prop) : (term31 P) = (term32 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319766 : term48 = term49.
Proof. exact (@lem1319765 term50). Qed.
Lemma lem1319767 (x : nadd) : (term51 x) = (term43 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1319768 : term52 = term45.
Proof. exact (fun_ext (fun x : nadd => @lem1319767 x)). Qed.
Lemma lem1319769 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319770 : term48 = term47.
Proof. exact (MK_COMB (@lem1319769) (@lem1319768)). Qed.
Lemma lem1319771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319772 : term53 = term54.
Proof. exact (MK_COMB (@lem1319771) (@lem1319770)). Qed.
Lemma lem1319773 (x : hreal) : (term55 x) = (term56 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1319774 : term57 = term50.
Proof. exact (fun_ext (fun x : hreal => @lem1319773 x)). Qed.
Lemma lem1319775 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319776 : term49 = term58.
Proof. exact (MK_COMB (@lem1319775) (@lem1319774)). Qed.
Lemma lem1319777 : (term48 = term49) = (term47 = term58).
Proof. exact (MK_COMB (@lem1319772) (@lem1319776)). Qed.
Lemma lem1319778 : term47 = term58.
Proof. exact (EQ_MP (@lem1319777) (@lem1319766)). Qed.
Lemma lem1319801 : term46 = term58.
Proof. exact (TRANS (@lem1319759) (@lem1319778)). Qed.
Lemma lem1319802 : term58.
Proof. exact (EQ_MP (@lem1319801) (@lem1276037)). Qed.
