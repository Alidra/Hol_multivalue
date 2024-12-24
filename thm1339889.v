Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339889_term_abbrevs.
Require Import TREAL_LE_LADD_IMP_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Lemma lem1339758 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339759 (y : prod hreal hreal) (z : prod hreal hreal) : (treal_le y z) = (term0 y z).
Proof. exact (@lem1339758 y z). Qed.
Lemma lem1339760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1339761 (y : prod hreal hreal) (z : prod hreal hreal) : (term1 y z) = (term2 y z).
Proof. exact (MK_COMB (@lem1339760) (@lem1339759 y z)). Qed.
Lemma lem1339763 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339764 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term3 y x z) = (term4 y x z).
Proof. exact (@lem1339763 (treal_add x y) (treal_add x z)). Qed.
Lemma lem1339766 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term5 x1 y1) = (term6 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1339767 (x : prod hreal hreal) (y : prod hreal hreal) : (term5 x y) = (term6 x y).
Proof. exact (@lem1339766 x y). Qed.
Lemma lem1339768 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1339769 (x : prod hreal hreal) (y : prod hreal hreal) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1339768) (@lem1339767 x y)). Qed.
Lemma lem1339771 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term5 x1 y1) = (term6 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1339772 (x : prod hreal hreal) (z : prod hreal hreal) : (term5 x z) = (term6 x z).
Proof. exact (@lem1339771 x z). Qed.
Lemma lem1339773 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term4 y x z) = (term9 y x z).
Proof. exact (MK_COMB (@lem1339769 x y) (@lem1339772 x z)). Qed.
Lemma lem1339774 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term3 y x z) = (term9 y x z).
Proof. exact (TRANS (@lem1339764 y x z) (@lem1339773 y x z)). Qed.
Lemma lem1339775 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term10 y x z) = (term11 y x z).
Proof. exact (MK_COMB (@lem1339761 y z) (@lem1339774 y x z)). Qed.
Lemma lem1339778 (y : prod hreal hreal) (x : prod hreal hreal) : (term12 y x) = (term13 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339775 y x z)). Qed.
Lemma lem1339779 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339780 (y : prod hreal hreal) (x : prod hreal hreal) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1339779) (@lem1339778 y x)). Qed.
Lemma lem1339786 (P : real -> Prop) : (term16 P) = (term17 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339787 (y : prod hreal hreal) (x : prod hreal hreal) : (term18 y x) = (term19 y x).
Proof. exact (@lem1339786 (term20 y x)). Qed.
Lemma lem1339788 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term21 y x z) = (term11 y x z).
Proof. exact (eq_refl (term21 y x z)). Qed.
Lemma lem1339789 (y : prod hreal hreal) (x : prod hreal hreal) : (term22 y x) = (term13 y x).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1339788 y x z)). Qed.
Lemma lem1339790 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339791 (y : prod hreal hreal) (x : prod hreal hreal) : (term18 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1339790) (@lem1339789 y x)). Qed.
Lemma lem1339792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339793 (y : prod hreal hreal) (x : prod hreal hreal) : (term23 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1339792) (@lem1339791 y x)). Qed.
Lemma lem1339794 (y : prod hreal hreal) (x : prod hreal hreal) (z : real) : (term25 y x z) = (term26 y x z).
Proof. exact (eq_refl (term25 y x z)). Qed.
Lemma lem1339795 (y : prod hreal hreal) (x : prod hreal hreal) : (term27 y x) = (term20 y x).
Proof. exact (fun_ext (fun z : real => @lem1339794 y x z)). Qed.
Lemma lem1339796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339797 (y : prod hreal hreal) (x : prod hreal hreal) : (term19 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1339796) (@lem1339795 y x)). Qed.
Lemma lem1339798 (y : prod hreal hreal) (x : prod hreal hreal) : ((term18 y x) = (term19 y x)) = ((term15 y x) = (term28 y x)).
Proof. exact (MK_COMB (@lem1339793 y x) (@lem1339797 y x)). Qed.
Lemma lem1339799 (y : prod hreal hreal) (x : prod hreal hreal) : (term15 y x) = (term28 y x).
Proof. exact (EQ_MP (@lem1339798 y x) (@lem1339787 y x)). Qed.
Lemma lem1339808 (y : prod hreal hreal) (x : prod hreal hreal) : (term14 y x) = (term28 y x).
Proof. exact (TRANS (@lem1339780 y x) (@lem1339799 y x)). Qed.
Lemma lem1339809 (x : prod hreal hreal) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339808 y x)). Qed.
Lemma lem1339810 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339811 (x : prod hreal hreal) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem1339810) (@lem1339809 x)). Qed.
Lemma lem1339817 (P : real -> Prop) : (term16 P) = (term17 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339818 (x : prod hreal hreal) : (term33 x) = (term34 x).
Proof. exact (@lem1339817 (term35 x)). Qed.
Lemma lem1339819 (y : prod hreal hreal) (x : prod hreal hreal) : (term36 x y) = (term28 y x).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1339820 (x : prod hreal hreal) : (term37 x) = (term30 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339819 y x)). Qed.
Lemma lem1339821 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339822 (x : prod hreal hreal) : (term33 x) = (term32 x).
Proof. exact (MK_COMB (@lem1339821) (@lem1339820 x)). Qed.
Lemma lem1339823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339824 (x : prod hreal hreal) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1339823) (@lem1339822 x)). Qed.
Lemma lem1339825 (y : real) (x : prod hreal hreal) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1339826 (x : prod hreal hreal) : (term42 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1339825 y x)). Qed.
Lemma lem1339827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339828 (x : prod hreal hreal) : (term34 x) = (term43 x).
Proof. exact (MK_COMB (@lem1339827) (@lem1339826 x)). Qed.
Lemma lem1339829 (x : prod hreal hreal) : ((term33 x) = (term34 x)) = ((term32 x) = (term43 x)).
Proof. exact (MK_COMB (@lem1339824 x) (@lem1339828 x)). Qed.
Lemma lem1339830 (x : prod hreal hreal) : (term32 x) = (term43 x).
Proof. exact (EQ_MP (@lem1339829 x) (@lem1339818 x)). Qed.
Lemma lem1339845 (x : prod hreal hreal) : (term31 x) = (term43 x).
Proof. exact (TRANS (@lem1339811 x) (@lem1339830 x)). Qed.
Lemma lem1339846 : term44 = term45.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339845 x)). Qed.
Lemma lem1339847 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339848 : term46 = term47.
Proof. exact (MK_COMB (@lem1339847) (@lem1339846)). Qed.
Lemma lem1339854 (P : real -> Prop) : (term16 P) = (term17 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339855 : term48 = term49.
Proof. exact (@lem1339854 term50). Qed.
Lemma lem1339856 (x : prod hreal hreal) : (term51 x) = (term43 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1339857 : term52 = term45.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339856 x)). Qed.
Lemma lem1339858 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339859 : term48 = term47.
Proof. exact (MK_COMB (@lem1339858) (@lem1339857)). Qed.
Lemma lem1339860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339861 : term53 = term54.
Proof. exact (MK_COMB (@lem1339860) (@lem1339859)). Qed.
Lemma lem1339862 (x : real) : (term55 x) = (term56 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1339863 : term57 = term50.
Proof. exact (fun_ext (fun x : real => @lem1339862 x)). Qed.
Lemma lem1339864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339865 : term49 = term58.
Proof. exact (MK_COMB (@lem1339864) (@lem1339863)). Qed.
Lemma lem1339866 : (term48 = term49) = (term47 = term58).
Proof. exact (MK_COMB (@lem1339861) (@lem1339865)). Qed.
Lemma lem1339867 : term47 = term58.
Proof. exact (EQ_MP (@lem1339866) (@lem1339855)). Qed.
Lemma lem1339888 : term46 = term58.
Proof. exact (TRANS (@lem1339848) (@lem1339867)). Qed.
Lemma lem1339889 : term58.
Proof. exact (EQ_MP (@lem1339888) (@lem1331249)). Qed.
