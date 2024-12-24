Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_RZERO_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1517839 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517840 : term2 = term3.
Proof. exact (@lem1517839 term4). Qed.
Lemma lem1517841 (x : real) : (term5 x) = ((term6 x) = x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1517842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517844 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1517842) (@lem1517841 x)). Qed.
Lemma lem1517845 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1517844 x)). Qed.
Lemma lem1517846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517847 : term3 = term11.
Proof. exact (MK_COMB (@lem1517846) (@lem1517845)). Qed.
Lemma lem1517849 : term2 = term11.
Proof. exact (TRANS (@lem1517840) (@lem1517847)). Qed.
Lemma lem1517852 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1517853 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1517852 x)). Qed.
Lemma lem1517854 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517855 : term11 = term11.
Proof. exact (MK_COMB (@lem1517854) (@lem1517853)). Qed.
Lemma lem1517856 : term2 = term11.
Proof. exact (TRANS (@lem1517849) (@lem1517855)). Qed.
Lemma lem1517857 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (term6 x) x). Qed.
Lemma lem1517858 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517864 (x : real) : (term6 x) = (term13 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1517866 (x : nat) : (term15 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1517867 : term16 = term14.
Proof. exact (@lem1517866 term17). Qed.
Lemma lem1517868 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1517869 (x : real) : (term13 x) = (term18 x).
Proof. exact (MK_COMB (@lem1517868 x) (@lem1517867)). Qed.
Lemma lem1517870 (x : real) : (term18 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1517871 (x : real) : (term13 x) = x.
Proof. exact (TRANS (@lem1517869 x) (@lem1517870 x)). Qed.
Lemma lem1517873 (x : real) : (term6 x) = x.
Proof. exact (TRANS (@lem1517864 x) (@lem1517871 x)). Qed.
Lemma lem1517874 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1517875 (x : real) : (term19 x) = (real_sub x).
Proof. exact (MK_COMB (@lem1517874) (@lem1517873 x)). Qed.
Lemma lem1517876 (x : real) : (term20 x) = (real_sub x x).
Proof. exact (MK_COMB (@lem1517875 x) (@lem1517858 x)). Qed.
Lemma lem1517877 (x : real) : (real_sub x x) = (term21 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1517881 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1517883 (m : nat) : (term24 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517884 : term25 = term14.
Proof. exact (@lem1517883 term17). Qed.
Lemma lem1517885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517886 : term26 = term27.
Proof. exact (MK_COMB (@lem1517885) (@lem1517884)). Qed.
Lemma lem1517887 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517888 (x : real) : (term22 x) = (term28 x).
Proof. exact (MK_COMB (@lem1517886) (@lem1517887 x)). Qed.
Lemma lem1517889 (x : real) : (term21 x) = (term28 x).
Proof. exact (TRANS (@lem1517881 x) (@lem1517888 x)). Qed.
Lemma lem1517890 (x : real) : (term28 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1517892 (x : real) : (term21 x) = term14.
Proof. exact (TRANS (@lem1517889 x) (@lem1517890 x)). Qed.
Lemma lem1517893 (x : real) : (real_sub x x) = term14.
Proof. exact (TRANS (@lem1517877 x) (@lem1517892 x)). Qed.
Lemma lem1517894 (x : real) : (term20 x) = term14.
Proof. exact (TRANS (@lem1517876 x) (@lem1517893 x)). Qed.
Lemma lem1517895 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1517896 (x : real) : (term29 x) = term30.
Proof. exact (MK_COMB (@lem1517895) (@lem1517894 x)). Qed.
Lemma lem1517897 : term30 = term16.
Proof. exact (@lem1483512 term14). Qed.
Lemma lem1517899 (x : nat) : (term15 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1517900 : term16 = term14.
Proof. exact (@lem1517899 term17). Qed.
Lemma lem1517901 : term30 = term14.
Proof. exact (TRANS (@lem1517897) (@lem1517900)). Qed.
Lemma lem1517902 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1517903 (x : real) : ((term29 x) = term30) = ((term29 x) = term14).
Proof. exact (MK_COMB (@lem1517902 x) (@lem1517901)). Qed.
Lemma lem1517904 (x : real) : (term29 x) = term14.
Proof. exact (EQ_MP (@lem1517903 x) (@lem1517896 x)). Qed.
Lemma lem1517905 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517906 (x : real) : (term32 x) = term33.
Proof. exact (MK_COMB (@lem1517905) (@lem1517904 x)). Qed.
Lemma lem1517907 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1517908 (x : real) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem1517906 x) (@lem1517907)). Qed.
Lemma lem1517909 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517910 (x : real) : (term36 x) = term33.
Proof. exact (MK_COMB (@lem1517909) (@lem1517894 x)). Qed.
Lemma lem1517911 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1517912 (x : real) : (term37 x) = term35.
Proof. exact (MK_COMB (@lem1517910 x) (@lem1517911)). Qed.
Lemma lem1517913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517914 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1517913) (@lem1517912 x)). Qed.
Lemma lem1517915 (x : real) : (term12 x) = term40.
Proof. exact (MK_COMB (@lem1517914 x) (@lem1517908 x)). Qed.
Lemma lem1517916 (x : real) : (term8 x) = term40.
Proof. exact (TRANS (@lem1517857 x) (@lem1517915 x)). Qed.
Lemma lem1517917 : term10 = term41.
Proof. exact (fun_ext (fun x : real => @lem1517916 x)). Qed.
Lemma lem1517918 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517919 : term11 = term42.
Proof. exact (MK_COMB (@lem1517918) (@lem1517917)). Qed.
Lemma lem1517920 : term2 = term42.
Proof. exact (TRANS (@lem1517856) (@lem1517919)). Qed.
Lemma lem1517922 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1517923 (P : real -> Prop) (Q : real -> Prop) : (term45 P Q) = (term46 P Q).
Proof. exact (@lem1517922 real P Q). Qed.
Lemma lem1517924 : term47 = term48.
Proof. exact (@lem1517923 term49 term49). Qed.
Lemma lem1517925 (x : real) : (term50 x) = term35.
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1517926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517927 (x : real) : (term51 x) = term39.
Proof. exact (MK_COMB (@lem1517926) (@lem1517925 x)). Qed.
Lemma lem1517928 (x : real) : (term50 x) = term35.
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1517929 (x : real) : (term52 x) = term40.
Proof. exact (MK_COMB (@lem1517927 x) (@lem1517928 x)). Qed.
Lemma lem1517930 : term53 = term41.
Proof. exact (fun_ext (fun x : real => @lem1517929 x)). Qed.
Lemma lem1517931 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517932 : term47 = term42.
Proof. exact (MK_COMB (@lem1517931) (@lem1517930)). Qed.
Lemma lem1517933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1517934 : term54 = term55.
Proof. exact (MK_COMB (@lem1517933) (@lem1517932)). Qed.
Lemma lem1517935 (x : real) : (term50 x) = term35.
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1517936 : term56 = term49.
Proof. exact (fun_ext (fun x : real => @lem1517935 x)). Qed.
Lemma lem1517937 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517938 : term57 = term58.
Proof. exact (MK_COMB (@lem1517937) (@lem1517936)). Qed.
Lemma lem1517939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517940 : term59 = term60.
Proof. exact (MK_COMB (@lem1517939) (@lem1517938)). Qed.
Lemma lem1517941 (x : real) : (term50 x) = term35.
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1517942 : term56 = term49.
Proof. exact (fun_ext (fun x : real => @lem1517941 x)). Qed.
Lemma lem1517943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517944 : term57 = term58.
Proof. exact (MK_COMB (@lem1517943) (@lem1517942)). Qed.
Lemma lem1517945 : term48 = term61.
Proof. exact (MK_COMB (@lem1517940) (@lem1517944)). Qed.
Lemma lem1517946 : (term47 = term48) = (term42 = term61).
Proof. exact (MK_COMB (@lem1517934) (@lem1517945)). Qed.
Lemma lem1517947 : term42 = term61.
Proof. exact (EQ_MP (@lem1517946) (@lem1517924)). Qed.
Lemma lem1517949 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517950 (t : Prop) : (term63 t) = t.
Proof. exact (@lem1517949 real t). Qed.
Lemma lem1517951 : term58 = term35.
Proof. exact (@lem1517950 term35). Qed.
Lemma lem1517952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517953 : term60 = term39.
Proof. exact (MK_COMB (@lem1517952) (@lem1517951)). Qed.
Lemma lem1517955 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517956 (t : Prop) : (term63 t) = t.
Proof. exact (@lem1517955 real t). Qed.
Lemma lem1517957 : term58 = term35.
Proof. exact (@lem1517956 term35). Qed.
Lemma lem1517958 : term61 = term40.
Proof. exact (MK_COMB (@lem1517953) (@lem1517957)). Qed.
Lemma lem1517961 : term42 = term40.
Proof. exact (TRANS (@lem1517947) (@lem1517958)). Qed.
Lemma lem1517970 : term2 = term40.
Proof. exact (TRANS (@lem1517920) (@lem1517961)). Qed.
Lemma lem1517980 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1517981 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1517983 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517984 : term35 = term65.
Proof. exact (@lem1517983 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517985 : term65 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517986 : term35 = False.
Proof. exact (TRANS (@lem1517984) (@lem1517985)). Qed.
Lemma lem1517987 (h1 : term35) : False.
Proof. exact (EQ_MP (@lem1517986) (@lem1517981 h1)). Qed.
Lemma lem1517988 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1517990 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517991 : term35 = term65.
Proof. exact (@lem1517990 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517992 : term65 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517993 : term35 = False.
Proof. exact (TRANS (@lem1517991) (@lem1517992)). Qed.
Lemma lem1517994 (h1 : term35) : False.
Proof. exact (EQ_MP (@lem1517993) (@lem1517988 h1)). Qed.
Lemma lem1517995 (h1 : term40) : False.
Proof. exact (or_elim (@lem1517980 h1) (fun h0 : term35 => @lem1517987 h0) (fun h0 : term35 => @lem1517994 h0)). Qed.
Lemma lem1517997 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1517998 (h1 : term40) : term40 = False.
Proof. exact (prop_ext (fun h2 : term40 => @lem1517995 h1) (fun h2 : False => @lem1517997 h1)). Qed.
Lemma lem1517999 (h1 : term40) : False.
Proof. exact (EQ_MP (@lem1517998 h1) (@lem1517997 h1)). Qed.
Lemma lem1518000 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1518001 (h1 : term2) : term40.
Proof. exact (EQ_MP (@lem1517970) (@lem1518000 h1)). Qed.
Lemma lem1518002 (h1 : term2) : term40 = False.
Proof. exact (prop_ext (fun h2 : term40 => @lem1517999 h2) (fun h2 : False => @lem1518001 h1)). Qed.
Lemma lem1518003 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1518002 h1) (@lem1518001 h1)). Qed.
Lemma lem1518004 : term66.
Proof. exact (fun h0 : term2 => @lem1518003 h0). Qed.
Lemma lem1518005 : term67.
Proof. exact (@lem1386578 term68). Qed.
Lemma lem1518006 : term68.
Proof. exact (@lem1518005 (@lem1518004)). Qed.
