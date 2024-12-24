Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338912_term_abbrevs.
Require Import TREAL_MUL_ASSOC_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338771 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338772 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term1 x y z) = ((term2 x y z) = (term3 x y z)).
Proof. exact (@lem1338771 (term4 x y z) (term5 x y z)). Qed.
Lemma lem1338776 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338777 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1338776 x (treal_mul y z)). Qed.
Lemma lem1338779 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338780 (y : prod hreal hreal) (z : prod hreal hreal) : (term6 y z) = (term7 y z).
Proof. exact (@lem1338779 y z). Qed.
Lemma lem1338781 (x : prod hreal hreal) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1338782 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term8 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1338781 x) (@lem1338780 y z)). Qed.
Lemma lem1338783 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term10 x y z).
Proof. exact (TRANS (@lem1338777 x y z) (@lem1338782 x y z)). Qed.
Lemma lem1338784 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338785 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1338784) (@lem1338783 x y z)). Qed.
Lemma lem1338787 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338788 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term3 x y z) = (term13 x y z).
Proof. exact (@lem1338787 (treal_mul x y) z). Qed.
Lemma lem1338790 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338791 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (@lem1338790 x y). Qed.
Lemma lem1338792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1338793 (x : prod hreal hreal) (y : prod hreal hreal) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1338792) (@lem1338791 x y)). Qed.
Lemma lem1338794 (z : prod hreal hreal) : (term0 z) = (term0 z).
Proof. exact (eq_refl (term0 z)). Qed.
Lemma lem1338795 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term13 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem1338793 x y) (@lem1338794 z)). Qed.
Lemma lem1338796 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term3 x y z) = (term16 x y z).
Proof. exact (TRANS (@lem1338788 x y z) (@lem1338795 x y z)). Qed.
Lemma lem1338797 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : ((term2 x y z) = (term3 x y z)) = ((term10 x y z) = (term16 x y z)).
Proof. exact (MK_COMB (@lem1338785 x y z) (@lem1338796 x y z)). Qed.
Lemma lem1338800 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term1 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (TRANS (@lem1338772 x y z) (@lem1338797 x y z)). Qed.
Lemma lem1338801 (x : prod hreal hreal) (y : prod hreal hreal) : (term17 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1338800 x y z)). Qed.
Lemma lem1338802 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338803 (x : prod hreal hreal) (y : prod hreal hreal) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1338802) (@lem1338801 x y)). Qed.
Lemma lem1338809 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338810 (x : prod hreal hreal) (y : prod hreal hreal) : (term23 x y) = (term24 x y).
Proof. exact (@lem1338809 (term25 x y)). Qed.
Lemma lem1338811 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term26 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1338812 (x : prod hreal hreal) (y : prod hreal hreal) : (term27 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1338811 x y z)). Qed.
Lemma lem1338813 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338814 (x : prod hreal hreal) (y : prod hreal hreal) : (term23 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1338813) (@lem1338812 x y)). Qed.
Lemma lem1338815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338816 (x : prod hreal hreal) (y : prod hreal hreal) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1338815) (@lem1338814 x y)). Qed.
Lemma lem1338817 (x : prod hreal hreal) (y : prod hreal hreal) (z : real) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1338818 (x : prod hreal hreal) (y : prod hreal hreal) : (term33 x y) = (term25 x y).
Proof. exact (fun_ext (fun z : real => @lem1338817 x y z)). Qed.
Lemma lem1338819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338820 (x : prod hreal hreal) (y : prod hreal hreal) : (term24 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1338819) (@lem1338818 x y)). Qed.
Lemma lem1338821 (x : prod hreal hreal) (y : prod hreal hreal) : ((term23 x y) = (term24 x y)) = ((term20 x y) = (term34 x y)).
Proof. exact (MK_COMB (@lem1338816 x y) (@lem1338820 x y)). Qed.
Lemma lem1338822 (x : prod hreal hreal) (y : prod hreal hreal) : (term20 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem1338821 x y) (@lem1338810 x y)). Qed.
Lemma lem1338831 (x : prod hreal hreal) (y : prod hreal hreal) : (term19 x y) = (term34 x y).
Proof. exact (TRANS (@lem1338803 x y) (@lem1338822 x y)). Qed.
Lemma lem1338832 (x : prod hreal hreal) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338831 x y)). Qed.
Lemma lem1338833 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338834 (x : prod hreal hreal) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1338833) (@lem1338832 x)). Qed.
Lemma lem1338840 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338841 (x : prod hreal hreal) : (term39 x) = (term40 x).
Proof. exact (@lem1338840 (term41 x)). Qed.
Lemma lem1338842 (x : prod hreal hreal) (y : prod hreal hreal) : (term42 x y) = (term34 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1338843 (x : prod hreal hreal) : (term43 x) = (term36 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338842 x y)). Qed.
Lemma lem1338844 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338845 (x : prod hreal hreal) : (term39 x) = (term38 x).
Proof. exact (MK_COMB (@lem1338844) (@lem1338843 x)). Qed.
Lemma lem1338846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338847 (x : prod hreal hreal) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1338846) (@lem1338845 x)). Qed.
Lemma lem1338848 (x : prod hreal hreal) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1338849 (x : prod hreal hreal) : (term48 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1338848 x y)). Qed.
Lemma lem1338850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338851 (x : prod hreal hreal) : (term40 x) = (term49 x).
Proof. exact (MK_COMB (@lem1338850) (@lem1338849 x)). Qed.
Lemma lem1338852 (x : prod hreal hreal) : ((term39 x) = (term40 x)) = ((term38 x) = (term49 x)).
Proof. exact (MK_COMB (@lem1338847 x) (@lem1338851 x)). Qed.
Lemma lem1338853 (x : prod hreal hreal) : (term38 x) = (term49 x).
Proof. exact (EQ_MP (@lem1338852 x) (@lem1338841 x)). Qed.
Lemma lem1338868 (x : prod hreal hreal) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1338834 x) (@lem1338853 x)). Qed.
Lemma lem1338869 : term50 = term51.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338868 x)). Qed.
Lemma lem1338870 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338871 : term52 = term53.
Proof. exact (MK_COMB (@lem1338870) (@lem1338869)). Qed.
Lemma lem1338877 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338878 : term54 = term55.
Proof. exact (@lem1338877 term56). Qed.
Lemma lem1338879 (x : prod hreal hreal) : (term57 x) = (term49 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1338880 : term58 = term51.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338879 x)). Qed.
Lemma lem1338881 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338882 : term54 = term53.
Proof. exact (MK_COMB (@lem1338881) (@lem1338880)). Qed.
Lemma lem1338883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338884 : term59 = term60.
Proof. exact (MK_COMB (@lem1338883) (@lem1338882)). Qed.
Lemma lem1338885 (x : real) : (term61 x) = (term62 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1338886 : term63 = term56.
Proof. exact (fun_ext (fun x : real => @lem1338885 x)). Qed.
Lemma lem1338887 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338888 : term55 = term64.
Proof. exact (MK_COMB (@lem1338887) (@lem1338886)). Qed.
Lemma lem1338889 : (term54 = term55) = (term53 = term64).
Proof. exact (MK_COMB (@lem1338884) (@lem1338888)). Qed.
Lemma lem1338890 : term53 = term64.
Proof. exact (EQ_MP (@lem1338889) (@lem1338878)). Qed.
Lemma lem1338911 : term52 = term64.
Proof. exact (TRANS (@lem1338871) (@lem1338890)). Qed.
Lemma lem1338912 : term64.
Proof. exact (EQ_MP (@lem1338911) (@lem1329092)). Qed.
