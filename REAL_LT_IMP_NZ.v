Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_IMP_NZ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1523758 (x : real) : (term0 x) = (x = term1).
Proof. exact (@lem16933 (x = term1)). Qed.
Lemma lem1523760 (x : real) : (term2 x) = (term2 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1523761 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1523760 x) (@lem1523758 x)). Qed.
Lemma lem1523762 (x : real) : (term5 x) = (term3 x).
Proof. exact (@lem17362 (term6 x) (term7 x)). Qed.
Lemma lem1523763 (x : real) : (term5 x) = (term4 x).
Proof. exact (TRANS (@lem1523762 x) (@lem1523761 x)). Qed.
Lemma lem1523764 (P : real -> Prop) : (term8 P) = (term9 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523765 : term10 = term11.
Proof. exact (@lem1523764 term12). Qed.
Lemma lem1523766 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1523767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523768 (x : real) : (term15 x) = (term5 x).
Proof. exact (MK_COMB (@lem1523767) (@lem1523766 x)). Qed.
Lemma lem1523769 (x : real) : (term15 x) = (term4 x).
Proof. exact (TRANS (@lem1523768 x) (@lem1523763 x)). Qed.
Lemma lem1523770 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem1523769 x)). Qed.
Lemma lem1523771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523772 : term11 = term18.
Proof. exact (MK_COMB (@lem1523771) (@lem1523770)). Qed.
Lemma lem1523774 : term10 = term18.
Proof. exact (TRANS (@lem1523765) (@lem1523772)). Qed.
Lemma lem1523779 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1523780 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1523779 x)). Qed.
Lemma lem1523781 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523782 : term18 = term18.
Proof. exact (MK_COMB (@lem1523781) (@lem1523780)). Qed.
Lemma lem1523783 : term10 = term18.
Proof. exact (TRANS (@lem1523774) (@lem1523782)). Qed.
Lemma lem1523784 (x : real) : (term6 x) = (term19 x).
Proof. exact (@lem1483521 x term1). Qed.
Lemma lem1523790 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1523792 (x : nat) : (term22 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1523793 : term23 = term1.
Proof. exact (@lem1523792 term24). Qed.
Lemma lem1523794 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1523795 (x : real) : (term21 x) = (term25 x).
Proof. exact (MK_COMB (@lem1523794 x) (@lem1523793)). Qed.
Lemma lem1523796 (x : real) : (term25 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1523797 (x : real) : (term21 x) = x.
Proof. exact (TRANS (@lem1523795 x) (@lem1523796 x)). Qed.
Lemma lem1523799 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1523790 x) (@lem1523797 x)). Qed.
Lemma lem1523800 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523801 (x : real) : (term26 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1523800) (@lem1523799 x)). Qed.
Lemma lem1523802 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1523803 (x : real) : (term19 x) = (term27 x).
Proof. exact (MK_COMB (@lem1523801 x) (@lem1523802)). Qed.
Lemma lem1523804 (x : real) : (term6 x) = (term27 x).
Proof. exact (TRANS (@lem1523784 x) (@lem1523803 x)). Qed.
Lemma lem1523805 (x : real) : (x = term1) = ((term20 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1523811 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1523813 (x : nat) : (term22 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1523814 : term23 = term1.
Proof. exact (@lem1523813 term24). Qed.
Lemma lem1523815 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1523816 (x : real) : (term21 x) = (term25 x).
Proof. exact (MK_COMB (@lem1523815 x) (@lem1523814)). Qed.
Lemma lem1523817 (x : real) : (term25 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1523818 (x : real) : (term21 x) = x.
Proof. exact (TRANS (@lem1523816 x) (@lem1523817 x)). Qed.
Lemma lem1523820 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1523811 x) (@lem1523818 x)). Qed.
Lemma lem1523821 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1523822 (x : real) : (term28 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1523821) (@lem1523820 x)). Qed.
Lemma lem1523823 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1523824 (x : real) : ((term20 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1523822 x) (@lem1523823)). Qed.
Lemma lem1523825 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1523805 x) (@lem1523824 x)). Qed.
Lemma lem1523826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1523827 (x : real) : (term2 x) = (term29 x).
Proof. exact (MK_COMB (@lem1523826) (@lem1523804 x)). Qed.
Lemma lem1523828 (x : real) : (term4 x) = (term30 x).
Proof. exact (MK_COMB (@lem1523827 x) (@lem1523825 x)). Qed.
Lemma lem1523829 : term17 = term31.
Proof. exact (fun_ext (fun x : real => @lem1523828 x)). Qed.
Lemma lem1523830 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523831 : term18 = term32.
Proof. exact (MK_COMB (@lem1523830) (@lem1523829)). Qed.
Lemma lem1523886 : term10 = term32.
Proof. exact (TRANS (@lem1523783) (@lem1523831)). Qed.
Lemma lem1523893 (x : real) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1523894 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1523893 x)). Qed.
Lemma lem1523895 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523896 : term32 = term32.
Proof. exact (MK_COMB (@lem1523895) (@lem1523894)). Qed.
Lemma lem1523897 : term10 = term32.
Proof. exact (TRANS (@lem1523886) (@lem1523896)). Qed.
Lemma lem1523901 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1523902 (x : real) (h1 : term30 x) : x = term1.
Proof. exact (proj2 (@lem1523901 x h1)). Qed.
Lemma lem1523903 (x : real) (h1 : term30 x) : term27 x.
Proof. exact (proj1 (@lem1523901 x h1)). Qed.
Lemma lem1523905 (n : nat) (m : nat) : (term33 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523906 : term34 = term35.
Proof. exact (@lem1523905 (NUMERAL 0) term24). Qed.
Lemma lem1523907 : term36 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1523908 (h1 : term36 = (BIT1 0)) : term35 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1523909 : (term36 = (BIT1 0)) = (term35 = True).
Proof. exact (prop_ext (fun h1 : term36 = (BIT1 0) => @lem1523908 h1) (fun h1 : term35 = True => @lem1523907)). Qed.
Lemma lem1523910 : term35 = True.
Proof. exact (EQ_MP (@lem1523909) (@lem1523907)). Qed.
Lemma lem1523911 : term34 = True.
Proof. exact (TRANS (@lem1523906) (@lem1523910)). Qed.
Lemma lem1523912 : True = term34.
Proof. exact (SYM (@lem1523911)). Qed.
Lemma lem1523913 : term34.
Proof. exact (EQ_MP (@lem1523912) (@lem0)). Qed.
Lemma lem1523914 (x : real) (h1 : term30 x) : term37 x.
Proof. exact (conj (@lem1523913) (@lem1523903 x h1)). Qed.
Lemma lem1523916 (x : real) (y : real) : term38 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1523917 (x : real) : term39 x.
Proof. exact (@lem1523916 term40 x). Qed.
Lemma lem1523918 (x : real) (h1 : term30 x) : term41 x.
Proof. exact (@lem1523917 x (@lem1523914 x h1)). Qed.
Lemma lem1523919 (x : real) : (term42 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1523920 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523921 (x : real) : (term43 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1523920) (@lem1523919 x)). Qed.
Lemma lem1523922 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1523923 (x : real) : (term41 x) = (term27 x).
Proof. exact (MK_COMB (@lem1523921 x) (@lem1523922)). Qed.
Lemma lem1523924 (x : real) (h1 : term30 x) : term27 x.
Proof. exact (EQ_MP (@lem1523923 x) (@lem1523918 x h1)). Qed.
Lemma lem1523926 (y : real) : term44 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1523927 (x : real) : term44 x.
Proof. exact (@lem1523926 x). Qed.
Lemma lem1523928 (x : real) (h1 : term30 x) : term45 x.
Proof. exact (@lem1523927 x (@lem1523902 x h1)). Qed.
Lemma lem1523929 (x : real) (h1 : term30 x) : term46 x.
Proof. exact (@lem1523928 x h1 term47). Qed.
Lemma lem1523930 (x : real) : (term46 x) = ((term48 x) = term1).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1523937 (x : real) (h1 : term30 x) : (term48 x) = term1.
Proof. exact (EQ_MP (@lem1523930 x) (@lem1523929 x h1)). Qed.
Lemma lem1523938 (x : real) (h1 : term30 x) : term49 x.
Proof. exact (conj (@lem1523937 x h1) (@lem1523924 x h1)). Qed.
Lemma lem1523940 (x : real) (y : real) : term50 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1523941 (x : real) : term51 x.
Proof. exact (@lem1523940 (term48 x) x). Qed.
Lemma lem1523942 (x : real) (h1 : term30 x) : term52 x.
Proof. exact (@lem1523941 x (@lem1523938 x h1)). Qed.
Lemma lem1523943 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1523945 (m : nat) : (term55 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523946 : term56 = term1.
Proof. exact (@lem1523945 term24). Qed.
Lemma lem1523947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523948 : term57 = term58.
Proof. exact (MK_COMB (@lem1523947) (@lem1523946)). Qed.
Lemma lem1523949 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1523950 (x : real) : (term54 x) = (term59 x).
Proof. exact (MK_COMB (@lem1523948) (@lem1523949 x)). Qed.
Lemma lem1523951 (x : real) : (term53 x) = (term59 x).
Proof. exact (TRANS (@lem1523943 x) (@lem1523950 x)). Qed.
Lemma lem1523952 (x : real) : (term59 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1523953 (x : real) : (term53 x) = term1.
Proof. exact (TRANS (@lem1523951 x) (@lem1523952 x)). Qed.
Lemma lem1523954 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523955 (x : real) : (term60 x) = term61.
Proof. exact (MK_COMB (@lem1523954) (@lem1523953 x)). Qed.
Lemma lem1523956 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1523957 (x : real) : (term52 x) = term62.
Proof. exact (MK_COMB (@lem1523955 x) (@lem1523956)). Qed.
Lemma lem1523958 (x : real) (h1 : term30 x) : term62.
Proof. exact (EQ_MP (@lem1523957 x) (@lem1523942 x h1)). Qed.
Lemma lem1523960 (n : nat) (m : nat) : (term33 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523961 : term62 = term63.
Proof. exact (@lem1523960 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523962 : term63 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523963 : term62 = False.
Proof. exact (TRANS (@lem1523961) (@lem1523962)). Qed.
Lemma lem1523964 (x : real) (h1 : term30 x) : False.
Proof. exact (EQ_MP (@lem1523963) (@lem1523958 x h1)). Qed.
Lemma lem1523966 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1523967 (x : real) (h1 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h2 : term30 x => @lem1523964 x h1) (fun h2 : False => @lem1523966 x h1)). Qed.
Lemma lem1523968 (x : real) (h1 : term30 x) : False.
Proof. exact (EQ_MP (@lem1523967 x h1) (@lem1523966 x h1)). Qed.
Lemma lem1523969 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1523970 (h1 : term32) : False.
Proof. exact (ex_elim (@lem1523969 h1) (fun x : real => fun h0 : term31 x => @lem1523968 x h0)). Qed.
Lemma lem1523971 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1523972 (h1 : term10) : term32.
Proof. exact (EQ_MP (@lem1523897) (@lem1523971 h1)). Qed.
Lemma lem1523973 (h1 : term10) : term32 = False.
Proof. exact (prop_ext (fun h2 : term32 => @lem1523970 h2) (fun h2 : False => @lem1523972 h1)). Qed.
Lemma lem1523974 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1523973 h1) (@lem1523972 h1)). Qed.
Lemma lem1523975 : term64.
Proof. exact (fun h0 : term10 => @lem1523974 h0). Qed.
Lemma lem1523976 : term65.
Proof. exact (@lem1386578 term66). Qed.
Lemma lem1523977 : term66.
Proof. exact (@lem1523976 (@lem1523975)). Qed.
