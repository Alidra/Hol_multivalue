Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2525073_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_DIVMOD_UNIQ_spec.
Require Import INT_DIV_0_spec.
Require Import INT_REM_0_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2522864 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2522865 (m : int) (h1 : term0) : term1 m.
Proof. exact (@lem2522864 h1 m). Qed.
Lemma lem2522866 (m : int) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2522867 (m : int) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem2522866 m) (@lem2522865 m h1)). Qed.
Lemma lem2522868 (m : int) (n : int) (h1 : term0) : term3 m n.
Proof. exact (@lem2522867 m h1 n). Qed.
Lemma lem2522869 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2522870 (m : int) (n : int) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem2522869 m n) (@lem2522868 m n h1)). Qed.
Lemma lem2522871 (m : int) (n : int) (q : int) (h1 : term0) : term5 m n q.
Proof. exact (@lem2522870 m n h1 q). Qed.
Lemma lem2522872 (q : int) (m : int) (n : int) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem2522873 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem2522872 q m n) (@lem2522871 m n q h1)). Qed.
Lemma lem2522874 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term7 q m n r.
Proof. exact (@lem2522873 q m n h1 r). Qed.
Lemma lem2522875 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2522876 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem2522875 q m n r) (@lem2522874 q m n r h1)). Qed.
Lemma lem2522877 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem2522878 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2522876 q m n r h1 (@lem2522877 m q r n h2)). Qed.
Lemma lem2522879 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem2522878 m q r n h0 h1). Qed.
Lemma lem2522880 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2522881 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2522879 m q r n h2 (@lem2522880 h1)). Qed.
Lemma lem2522882 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem2522881 m q r n h1 h0). Qed.
Lemma lem2522883 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (fun r : int => @lem2522882 q m n r h1). Qed.
Lemma lem2522884 (q : int) (m : int) (h1 : term0) : term12 q m.
Proof. exact (fun n : int => @lem2522883 q m n h1). Qed.
Lemma lem2522885 (q : int) (h1 : term0) : term13 q.
Proof. exact (fun m : int => @lem2522884 q m h1). Qed.
Lemma lem2522886 (h1 : term0) : term14.
Proof. exact (fun q : int => @lem2522885 q h1). Qed.
Lemma lem2522887 : term15.
Proof. exact (fun h0 : term0 => @lem2522886 h0). Qed.
Lemma lem2522888 : term14.
Proof. exact (@lem2522887 (@lem2495588)). Qed.
Lemma lem2522889 (q : int) : term16 q.
Proof. exact (@lem2522888 q). Qed.
Lemma lem2522890 (q : int) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem2522891 (q : int) : term13 q.
Proof. exact (EQ_MP (@lem2522890 q) (@lem2522889 q)). Qed.
Lemma lem2522892 (q : int) (m : int) : term17 q m.
Proof. exact (@lem2522891 q m). Qed.
Lemma lem2522893 (q : int) (m : int) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem2522894 (q : int) (m : int) : term12 q m.
Proof. exact (EQ_MP (@lem2522893 q m) (@lem2522892 q m)). Qed.
Lemma lem2522895 (q : int) (m : int) (n : int) : term18 q m n.
Proof. exact (@lem2522894 q m n). Qed.
Lemma lem2522896 (q : int) (m : int) (n : int) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem2522897 (q : int) (m : int) (n : int) : term6 q m n.
Proof. exact (EQ_MP (@lem2522896 q m n) (@lem2522895 q m n)). Qed.
Lemma lem2522898 (q : int) (m : int) (n : int) (r : int) : term7 q m n r.
Proof. exact (@lem2522897 q m n r). Qed.
Lemma lem2522899 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2522901 (n : int) : term19 n.
Proof. exact (@lem9784 (n = term20)). Qed.
Lemma lem2522902 (n : int) : (term19 n) = (term21 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem2522903 (n : int) : term21 n.
Proof. exact (EQ_MP (@lem2522902 n) (@lem2522901 n)). Qed.
Lemma lem2522905 (n : int) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem2522906 {A : Type'} (P : A -> Prop) : term23 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2522907 {A : Type'} (P : A -> Prop) : (term23 A P) = (term24 A P).
Proof. exact (eq_refl (term23 A P)). Qed.
Lemma lem2522908 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (EQ_MP (@lem2522907 A P) (@lem2522906 A P)). Qed.
Lemma lem2522909 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term25 A P Q.
Proof. exact (@lem2522908 A P Q). Qed.
Lemma lem2522910 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term25 A P Q) = ((term26 A P Q) = (term27 A P Q)).
Proof. exact (eq_refl (term25 A P Q)). Qed.
Lemma lem2522913 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term26 A P Q) = (term27 A P Q).
Proof. exact (EQ_MP (@lem2522910 A P Q) (@lem2522909 A P Q)). Qed.
Lemma lem2522914 (P : int -> Prop) (Q : int -> Prop) : (term28 P Q) = (term29 P Q).
Proof. exact (@lem2522913 int P Q). Qed.
Lemma lem2522915 : term30 = term31.
Proof. exact (@lem2522914 term32 term33). Qed.
Lemma lem2522916 (n : int) : (term34 n) = ((term35 n) = term20).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem2522917 : term36 = term32.
Proof. exact (fun_ext (fun n : int => @lem2522916 n)). Qed.
Lemma lem2522918 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2522919 : term37 = term38.
Proof. exact (MK_COMB (@lem2522918) (@lem2522917)). Qed.
Lemma lem2522920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2522921 : term39 = term40.
Proof. exact (MK_COMB (@lem2522920) (@lem2522919)). Qed.
Lemma lem2522922 (n : int) : (term41 n) = ((term42 n) = term20).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem2522923 : term43 = term33.
Proof. exact (fun_ext (fun n : int => @lem2522922 n)). Qed.
Lemma lem2522924 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2522925 : term44 = term45.
Proof. exact (MK_COMB (@lem2522924) (@lem2522923)). Qed.
Lemma lem2522926 : term30 = term46.
Proof. exact (MK_COMB (@lem2522921) (@lem2522925)). Qed.
Lemma lem2522927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2522928 : term47 = term48.
Proof. exact (MK_COMB (@lem2522927) (@lem2522926)). Qed.
Lemma lem2522929 (n : int) : (term34 n) = ((term35 n) = term20).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem2522930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2522931 (n : int) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem2522930) (@lem2522929 n)). Qed.
Lemma lem2522932 (n : int) : (term41 n) = ((term42 n) = term20).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem2522933 (n : int) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem2522931 n) (@lem2522932 n)). Qed.
Lemma lem2522934 : term53 = term54.
Proof. exact (fun_ext (fun n : int => @lem2522933 n)). Qed.
Lemma lem2522935 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2522936 : term31 = term55.
Proof. exact (MK_COMB (@lem2522935) (@lem2522934)). Qed.
Lemma lem2522937 : (term30 = term31) = (term46 = term55).
Proof. exact (MK_COMB (@lem2522928) (@lem2522936)). Qed.
Lemma lem2522938 : term46 = term55.
Proof. exact (EQ_MP (@lem2522937) (@lem2522915)). Qed.
Lemma lem2522949 : term55 = term46.
Proof. exact (SYM (@lem2522938)). Qed.
Lemma lem2522950 (m : int) : term56 m.
Proof. exact (@lem2396893 m). Qed.
Lemma lem2522951 (m : int) : (term56 m) = ((term57 m) = m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem2522953 (m : int) : term58 m.
Proof. exact (@lem2395867 m). Qed.
Lemma lem2522954 (m : int) : (term58 m) = ((term59 m) = term20).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem2522961 (n : int) (h1 : n = term20) : n = term20.
Proof. exact (h1). Qed.
Lemma lem2522962 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem2522963 (n : int) (h1 : n = term20) : (term35 n) = term61.
Proof. exact (MK_COMB (@lem2522962) (@lem2522961 n h1)). Qed.
Lemma lem2522965 (m : int) : (term59 m) = term20.
Proof. exact (EQ_MP (@lem2522954 m) (@lem2522953 m)). Qed.
Lemma lem2522966 : term61 = term20.
Proof. exact (@lem2522965 term20). Qed.
Lemma lem2522967 (n : int) (h1 : n = term20) : (term35 n) = term20.
Proof. exact (TRANS (@lem2522963 n h1) (@lem2522966)). Qed.
Lemma lem2522968 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2522969 (n : int) (h1 : n = term20) : (term62 n) = term63.
Proof. exact (MK_COMB (@lem2522968) (@lem2522967 n h1)). Qed.
Lemma lem2522970 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2522971 (n : int) (h1 : n = term20) : ((term35 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2522969 n h1) (@lem2522970)). Qed.
Lemma lem2522973 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2522974 (x : int) : (x = x) = True.
Proof. exact (@lem2522973 int x). Qed.
Lemma lem2522975 : (term20 = term20) = True.
Proof. exact (@lem2522974 term20). Qed.
Lemma lem2522976 (n : int) (h1 : n = term20) : ((term35 n) = term20) = True.
Proof. exact (TRANS (@lem2522971 n h1) (@lem2522975)). Qed.
Lemma lem2522977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2522978 (n : int) (h1 : n = term20) : (term50 n) = (and True).
Proof. exact (MK_COMB (@lem2522977) (@lem2522976 n h1)). Qed.
Lemma lem2522982 (n : int) (h1 : n = term20) : n = term20.
Proof. exact (h1). Qed.
Lemma lem2522983 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem2522984 (n : int) (h1 : n = term20) : (term42 n) = term65.
Proof. exact (MK_COMB (@lem2522983) (@lem2522982 n h1)). Qed.
Lemma lem2522986 (m : int) : (term57 m) = m.
Proof. exact (EQ_MP (@lem2522951 m) (@lem2522950 m)). Qed.
Lemma lem2522987 : term65 = term20.
Proof. exact (@lem2522986 term20). Qed.
Lemma lem2522988 (n : int) (h1 : n = term20) : (term42 n) = term20.
Proof. exact (TRANS (@lem2522984 n h1) (@lem2522987)). Qed.
Lemma lem2522989 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2522990 (n : int) (h1 : n = term20) : (term66 n) = term63.
Proof. exact (MK_COMB (@lem2522989) (@lem2522988 n h1)). Qed.
Lemma lem2522991 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2522992 (n : int) (h1 : n = term20) : ((term42 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2522990 n h1) (@lem2522991)). Qed.
Lemma lem2522994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2522995 (x : int) : (x = x) = True.
Proof. exact (@lem2522994 int x). Qed.
Lemma lem2522996 : (term20 = term20) = True.
Proof. exact (@lem2522995 term20). Qed.
Lemma lem2522997 (n : int) (h1 : n = term20) : ((term42 n) = term20) = True.
Proof. exact (TRANS (@lem2522992 n h1) (@lem2522996)). Qed.
Lemma lem2522998 (n : int) (h1 : n = term20) : (term52 n) = (True /\ True).
Proof. exact (MK_COMB (@lem2522978 n h1) (@lem2522997 n h1)). Qed.
Lemma lem2523000 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2523001 : (True /\ True) = True.
Proof. exact (@lem2523000 True). Qed.
Lemma lem2523002 (n : int) (h1 : n = term20) : (term52 n) = True.
Proof. exact (TRANS (@lem2522998 n h1) (@lem2523001)). Qed.
Lemma lem2523003 (n : int) (h1 : n = term20) : True = (term52 n).
Proof. exact (SYM (@lem2523002 n h1)). Qed.
Lemma lem2523004 (n : int) (h1 : n = term20) : term52 n.
Proof. exact (EQ_MP (@lem2523003 n h1) (@lem0)). Qed.
Lemma lem2523033 (q : int) (m : int) (n : int) (r : int) : term8 q m n r.
Proof. exact (EQ_MP (@lem2522899 q m n r) (@lem2522898 q m n r)). Qed.
Lemma lem2523034 (n : int) : term67 n.
Proof. exact (@lem2523033 term20 term20 n term20). Qed.
Lemma lem2523035 (n : int) : (term68 n) = (term69 n).
Proof. exact (@lem2318604 (term69 n)). Qed.
Lemma lem2523055 (n : int) : (term70 n) = (term71 n).
Proof. exact (@lem17045 term72 (term73 n)). Qed.
Lemma lem2523057 (n : int) : (term74 n) = (term74 n).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem2523058 (n : int) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem2523057 n) (@lem2523055 n)). Qed.
Lemma lem2523059 (n : int) : (term77 n) = (term75 n).
Proof. exact (@lem17045 (term20 = (term78 n)) (term79 n)). Qed.
Lemma lem2523060 (n : int) : (term77 n) = (term76 n).
Proof. exact (TRANS (@lem2523059 n) (@lem2523058 n)). Qed.
Lemma lem2523062 (n : int) : (term80 n) = (term80 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem2523063 (n : int) : (term81 n) = (term82 n).
Proof. exact (MK_COMB (@lem2523062 n) (@lem2523060 n)). Qed.
Lemma lem2523064 (n : int) : (term83 n) = (term81 n).
Proof. exact (@lem17362 (term22 n) (term84 n)). Qed.
Lemma lem2523088 (n : int) : (term83 n) = (term82 n).
Proof. exact (TRANS (@lem2523064 n) (@lem2523063 n)). Qed.
Lemma lem2523090 (y : int) (x : int) : (term85 x y) = (term86 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2523091 (n : int) : (term22 n) = (term87 n).
Proof. exact (@lem2523090 term20 n). Qed.
Lemma lem2523093 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523094 (n : int) : (term89 n) = (term90 n).
Proof. exact (@lem2523093 (term91 n) term20). Qed.
Lemma lem2523096 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523097 (n : int) : (term94 n) = (term95 n).
Proof. exact (@lem2523096 n term96). Qed.
Lemma lem2523099 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523100 : term98 = term99.
Proof. exact (@lem2523099 term100). Qed.
Lemma lem2523101 (n : int) : (term101 n) = (term101 n).
Proof. exact (eq_refl (term101 n)). Qed.
Lemma lem2523102 (n : int) : (term95 n) = (term102 n).
Proof. exact (MK_COMB (@lem2523101 n) (@lem2523100)). Qed.
Lemma lem2523103 (n : int) : (term94 n) = (term102 n).
Proof. exact (TRANS (@lem2523097 n) (@lem2523102 n)). Qed.
Lemma lem2523104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523105 (n : int) : (term103 n) = (term104 n).
Proof. exact (MK_COMB (@lem2523104) (@lem2523103 n)). Qed.
Lemma lem2523107 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523108 : term105 = term106.
Proof. exact (@lem2523107 (NUMERAL 0)). Qed.
Lemma lem2523109 (n : int) : (term90 n) = (term107 n).
Proof. exact (MK_COMB (@lem2523105 n) (@lem2523108)). Qed.
Lemma lem2523110 (n : int) : (term89 n) = (term107 n).
Proof. exact (TRANS (@lem2523094 n) (@lem2523109 n)). Qed.
Lemma lem2523111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523112 (n : int) : (term108 n) = (term109 n).
Proof. exact (MK_COMB (@lem2523111) (@lem2523110 n)). Qed.
Lemma lem2523114 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523115 (n : int) : (term110 n) = (term111 n).
Proof. exact (@lem2523114 term112 n). Qed.
Lemma lem2523117 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523118 : term113 = term114.
Proof. exact (@lem2523117 term20 term96). Qed.
Lemma lem2523120 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523121 : term105 = term106.
Proof. exact (@lem2523120 (NUMERAL 0)). Qed.
Lemma lem2523122 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523123 : term115 = term116.
Proof. exact (MK_COMB (@lem2523122) (@lem2523121)). Qed.
Lemma lem2523125 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523126 : term98 = term99.
Proof. exact (@lem2523125 term100). Qed.
Lemma lem2523127 : term114 = term117.
Proof. exact (MK_COMB (@lem2523123) (@lem2523126)). Qed.
Lemma lem2523128 : term113 = term117.
Proof. exact (TRANS (@lem2523118) (@lem2523127)). Qed.
Lemma lem2523129 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523130 : term118 = term119.
Proof. exact (MK_COMB (@lem2523129) (@lem2523128)). Qed.
Lemma lem2523131 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2523132 (n : int) : (term111 n) = (term120 n).
Proof. exact (MK_COMB (@lem2523130) (@lem2523131 n)). Qed.
Lemma lem2523133 (n : int) : (term110 n) = (term120 n).
Proof. exact (TRANS (@lem2523115 n) (@lem2523132 n)). Qed.
Lemma lem2523134 (n : int) : (term87 n) = (term121 n).
Proof. exact (MK_COMB (@lem2523112 n) (@lem2523133 n)). Qed.
Lemma lem2523135 (n : int) : (term22 n) = (term121 n).
Proof. exact (TRANS (@lem2523091 n) (@lem2523134 n)). Qed.
Lemma lem2523137 (y : int) (x : int) : (term85 x y) = (term86 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2523138 (n : int) : (term122 n) = (term123 n).
Proof. exact (@lem2523137 (term78 n) term20). Qed.
Lemma lem2523140 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523141 (n : int) : (term124 n) = (term125 n).
Proof. exact (@lem2523140 term112 (term78 n)). Qed.
Lemma lem2523143 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523144 : term113 = term114.
Proof. exact (@lem2523143 term20 term96). Qed.
Lemma lem2523146 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523147 : term105 = term106.
Proof. exact (@lem2523146 (NUMERAL 0)). Qed.
Lemma lem2523148 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523149 : term115 = term116.
Proof. exact (MK_COMB (@lem2523148) (@lem2523147)). Qed.
Lemma lem2523151 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523152 : term98 = term99.
Proof. exact (@lem2523151 term100). Qed.
Lemma lem2523153 : term114 = term117.
Proof. exact (MK_COMB (@lem2523149) (@lem2523152)). Qed.
Lemma lem2523154 : term113 = term117.
Proof. exact (TRANS (@lem2523144) (@lem2523153)). Qed.
Lemma lem2523155 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523156 : term118 = term119.
Proof. exact (MK_COMB (@lem2523155) (@lem2523154)). Qed.
Lemma lem2523158 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523159 (n : int) : (term126 n) = (term127 n).
Proof. exact (@lem2523158 (term128 n) term20). Qed.
Lemma lem2523161 (x : int) (y : int) : (term129 x y) = (term130 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2523162 (n : int) : (term131 n) = (term132 n).
Proof. exact (@lem2523161 term20 n). Qed.
Lemma lem2523164 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523165 : term105 = term106.
Proof. exact (@lem2523164 (NUMERAL 0)). Qed.
Lemma lem2523166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523167 : term133 = term134.
Proof. exact (MK_COMB (@lem2523166) (@lem2523165)). Qed.
Lemma lem2523168 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2523169 (n : int) : (term132 n) = (term135 n).
Proof. exact (MK_COMB (@lem2523167) (@lem2523168 n)). Qed.
Lemma lem2523170 (n : int) : (term131 n) = (term135 n).
Proof. exact (TRANS (@lem2523162 n) (@lem2523169 n)). Qed.
Lemma lem2523171 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523172 (n : int) : (term136 n) = (term137 n).
Proof. exact (MK_COMB (@lem2523171) (@lem2523170 n)). Qed.
Lemma lem2523174 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523175 : term105 = term106.
Proof. exact (@lem2523174 (NUMERAL 0)). Qed.
Lemma lem2523176 (n : int) : (term127 n) = (term138 n).
Proof. exact (MK_COMB (@lem2523172 n) (@lem2523175)). Qed.
Lemma lem2523177 (n : int) : (term126 n) = (term138 n).
Proof. exact (TRANS (@lem2523159 n) (@lem2523176 n)). Qed.
Lemma lem2523178 (n : int) : (term125 n) = (term139 n).
Proof. exact (MK_COMB (@lem2523156) (@lem2523177 n)). Qed.
Lemma lem2523179 (n : int) : (term124 n) = (term139 n).
Proof. exact (TRANS (@lem2523141 n) (@lem2523178 n)). Qed.
Lemma lem2523180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523181 (n : int) : (term140 n) = (term141 n).
Proof. exact (MK_COMB (@lem2523180) (@lem2523179 n)). Qed.
Lemma lem2523183 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523184 (n : int) : (term142 n) = (term143 n).
Proof. exact (@lem2523183 (term144 n) term20). Qed.
Lemma lem2523186 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523187 (n : int) : (term145 n) = (term146 n).
Proof. exact (@lem2523186 (term78 n) term96). Qed.
Lemma lem2523189 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523190 (n : int) : (term126 n) = (term127 n).
Proof. exact (@lem2523189 (term128 n) term20). Qed.
Lemma lem2523192 (x : int) (y : int) : (term129 x y) = (term130 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2523193 (n : int) : (term131 n) = (term132 n).
Proof. exact (@lem2523192 term20 n). Qed.
Lemma lem2523195 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523196 : term105 = term106.
Proof. exact (@lem2523195 (NUMERAL 0)). Qed.
Lemma lem2523197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523198 : term133 = term134.
Proof. exact (MK_COMB (@lem2523197) (@lem2523196)). Qed.
Lemma lem2523199 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2523200 (n : int) : (term132 n) = (term135 n).
Proof. exact (MK_COMB (@lem2523198) (@lem2523199 n)). Qed.
Lemma lem2523201 (n : int) : (term131 n) = (term135 n).
Proof. exact (TRANS (@lem2523193 n) (@lem2523200 n)). Qed.
Lemma lem2523202 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523203 (n : int) : (term136 n) = (term137 n).
Proof. exact (MK_COMB (@lem2523202) (@lem2523201 n)). Qed.
Lemma lem2523205 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523206 : term105 = term106.
Proof. exact (@lem2523205 (NUMERAL 0)). Qed.
Lemma lem2523207 (n : int) : (term127 n) = (term138 n).
Proof. exact (MK_COMB (@lem2523203 n) (@lem2523206)). Qed.
Lemma lem2523208 (n : int) : (term126 n) = (term138 n).
Proof. exact (TRANS (@lem2523190 n) (@lem2523207 n)). Qed.
Lemma lem2523209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523210 (n : int) : (term147 n) = (term148 n).
Proof. exact (MK_COMB (@lem2523209) (@lem2523208 n)). Qed.
Lemma lem2523212 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523213 : term98 = term99.
Proof. exact (@lem2523212 term100). Qed.
Lemma lem2523214 (n : int) : (term146 n) = (term149 n).
Proof. exact (MK_COMB (@lem2523210 n) (@lem2523213)). Qed.
Lemma lem2523215 (n : int) : (term145 n) = (term149 n).
Proof. exact (TRANS (@lem2523187 n) (@lem2523214 n)). Qed.
Lemma lem2523216 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523217 (n : int) : (term150 n) = (term151 n).
Proof. exact (MK_COMB (@lem2523216) (@lem2523215 n)). Qed.
Lemma lem2523219 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523220 : term105 = term106.
Proof. exact (@lem2523219 (NUMERAL 0)). Qed.
Lemma lem2523221 (n : int) : (term143 n) = (term152 n).
Proof. exact (MK_COMB (@lem2523217 n) (@lem2523220)). Qed.
Lemma lem2523222 (n : int) : (term142 n) = (term152 n).
Proof. exact (TRANS (@lem2523184 n) (@lem2523221 n)). Qed.
Lemma lem2523223 (n : int) : (term123 n) = (term153 n).
Proof. exact (MK_COMB (@lem2523181 n) (@lem2523222 n)). Qed.
Lemma lem2523224 (n : int) : (term122 n) = (term153 n).
Proof. exact (TRANS (@lem2523138 n) (@lem2523223 n)). Qed.
Lemma lem2523226 (y : int) (x : int) : (term154 x y) = (term155 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2523227 : term156 = term157.
Proof. exact (@lem2523226 term20 term20). Qed.
Lemma lem2523229 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523230 : term157 = term158.
Proof. exact (@lem2523229 term112 term20). Qed.
Lemma lem2523232 (x : int) (y : int) : (term92 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2523233 : term113 = term114.
Proof. exact (@lem2523232 term20 term96). Qed.
Lemma lem2523235 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523236 : term105 = term106.
Proof. exact (@lem2523235 (NUMERAL 0)). Qed.
Lemma lem2523237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523238 : term115 = term116.
Proof. exact (MK_COMB (@lem2523237) (@lem2523236)). Qed.
Lemma lem2523240 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523241 : term98 = term99.
Proof. exact (@lem2523240 term100). Qed.
Lemma lem2523242 : term114 = term117.
Proof. exact (MK_COMB (@lem2523238) (@lem2523241)). Qed.
Lemma lem2523243 : term113 = term117.
Proof. exact (TRANS (@lem2523233) (@lem2523242)). Qed.
Lemma lem2523244 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523245 : term118 = term119.
Proof. exact (MK_COMB (@lem2523244) (@lem2523243)). Qed.
Lemma lem2523247 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523248 : term105 = term106.
Proof. exact (@lem2523247 (NUMERAL 0)). Qed.
Lemma lem2523249 : term158 = term159.
Proof. exact (MK_COMB (@lem2523245) (@lem2523248)). Qed.
Lemma lem2523250 : term157 = term159.
Proof. exact (TRANS (@lem2523230) (@lem2523249)). Qed.
Lemma lem2523251 : term156 = term159.
Proof. exact (TRANS (@lem2523227) (@lem2523250)). Qed.
Lemma lem2523253 (y : int) (x : int) : (term160 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2523254 (n : int) : (term161 n) = (term162 n).
Proof. exact (@lem2523253 (int_abs n) term20). Qed.
Lemma lem2523256 (x : int) (y : int) : (int_le x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2523257 (n : int) : (term162 n) = (term163 n).
Proof. exact (@lem2523256 (int_abs n) term20). Qed.
Lemma lem2523259 (x : int) : (term164 x) = (term165 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2523260 (n : int) : (term164 n) = (term165 n).
Proof. exact (@lem2523259 n). Qed.
Lemma lem2523261 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523262 (n : int) : (term166 n) = (term167 n).
Proof. exact (MK_COMB (@lem2523261) (@lem2523260 n)). Qed.
Lemma lem2523264 (n : nat) : (term97 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2523265 : term105 = term106.
Proof. exact (@lem2523264 (NUMERAL 0)). Qed.
Lemma lem2523266 (n : int) : (term163 n) = (term168 n).
Proof. exact (MK_COMB (@lem2523262 n) (@lem2523265)). Qed.
Lemma lem2523267 (n : int) : (term162 n) = (term168 n).
Proof. exact (TRANS (@lem2523257 n) (@lem2523266 n)). Qed.
Lemma lem2523268 (n : int) : (term161 n) = (term168 n).
Proof. exact (TRANS (@lem2523254 n) (@lem2523267 n)). Qed.
Lemma lem2523269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523270 : term169 = term170.
Proof. exact (MK_COMB (@lem2523269) (@lem2523251)). Qed.
Lemma lem2523271 (n : int) : (term71 n) = (term171 n).
Proof. exact (MK_COMB (@lem2523270) (@lem2523268 n)). Qed.
Lemma lem2523272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523273 (n : int) : (term74 n) = (term172 n).
Proof. exact (MK_COMB (@lem2523272) (@lem2523224 n)). Qed.
Lemma lem2523274 (n : int) : (term76 n) = (term173 n).
Proof. exact (MK_COMB (@lem2523273 n) (@lem2523271 n)). Qed.
Lemma lem2523275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2523276 (n : int) : (term80 n) = (term174 n).
Proof. exact (MK_COMB (@lem2523275) (@lem2523135 n)). Qed.
Lemma lem2523277 (n : int) : (term82 n) = (term175 n).
Proof. exact (MK_COMB (@lem2523276 n) (@lem2523274 n)). Qed.
Lemma lem2523278 (n : int) : (term83 n) = (term175 n).
Proof. exact (TRANS (@lem2523088 n) (@lem2523277 n)). Qed.
Lemma lem2523282 (t : Prop) : (term176 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2523338 (n : int) : (term177 n) = (term175 n).
Proof. exact (@lem2523282 (term175 n)). Qed.
Lemma lem2523339 (n : int) : (term107 n) = (term178 n).
Proof. exact (@lem1988287 term106 (term102 n)). Qed.
Lemma lem2523351 (n : int) : (term179 n) = (term180 n).
Proof. exact (@lem1982792 term106 (term102 n)). Qed.
Lemma lem2523352 (n : int) : (term181 n) = (term182 n).
Proof. exact (@lem1982781 (real_of_int n) term183 term99). Qed.
Lemma lem2523354 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523355 : term99 = term185.
Proof. exact (@lem2523354 term100). Qed.
Lemma lem2523357 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523358 : term183 = term188.
Proof. exact (@lem2523357 term100). Qed.
Lemma lem2523359 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523360 : term189 = term190.
Proof. exact (MK_COMB (@lem2523359) (@lem2523358)). Qed.
Lemma lem2523361 : term191 = term192.
Proof. exact (MK_COMB (@lem2523360) (@lem2523355)). Qed.
Lemma lem2523362 : term192 = term193.
Proof. exact (@lem1981613 term183 term99 term99 term99). Qed.
Lemma lem2523364 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2523365 : term196 = term197.
Proof. exact (@lem2523364 term100 term100). Qed.
Lemma lem2523366 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523367 : term199 = term100.
Proof. exact (EQ_MP (@lem2523366) (@lem940073)). Qed.
Lemma lem2523368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523369 : term197 = term99.
Proof. exact (MK_COMB (@lem2523368) (@lem2523367)). Qed.
Lemma lem2523370 : term196 = term99.
Proof. exact (TRANS (@lem2523365) (@lem2523369)). Qed.
Lemma lem2523372 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523373 : term191 = term202.
Proof. exact (@lem2523372 term100 term100). Qed.
Lemma lem2523374 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523375 : term199 = term100.
Proof. exact (EQ_MP (@lem2523374) (@lem940073)). Qed.
Lemma lem2523376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523377 : term197 = term99.
Proof. exact (MK_COMB (@lem2523376) (@lem2523375)). Qed.
Lemma lem2523378 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523379 : term202 = term183.
Proof. exact (MK_COMB (@lem2523378) (@lem2523377)). Qed.
Lemma lem2523380 : term191 = term183.
Proof. exact (TRANS (@lem2523373) (@lem2523379)). Qed.
Lemma lem2523381 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2523382 : term203 = term204.
Proof. exact (MK_COMB (@lem2523381) (@lem2523380)). Qed.
Lemma lem2523383 : term193 = term188.
Proof. exact (MK_COMB (@lem2523382) (@lem2523370)). Qed.
Lemma lem2523384 : term192 = term188.
Proof. exact (TRANS (@lem2523362) (@lem2523383)). Qed.
Lemma lem2523385 : term191 = term188.
Proof. exact (TRANS (@lem2523361) (@lem2523384)). Qed.
Lemma lem2523387 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2523388 : term188 = term183.
Proof. exact (@lem2523387 term183). Qed.
Lemma lem2523389 : term191 = term183.
Proof. exact (TRANS (@lem2523385) (@lem2523388)). Qed.
Lemma lem2523392 (n : int) : (term206 n) = (term206 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem2523393 (n : int) : (term182 n) = (term207 n).
Proof. exact (MK_COMB (@lem2523392 n) (@lem2523389)). Qed.
Lemma lem2523394 (n : int) : (term181 n) = (term207 n).
Proof. exact (TRANS (@lem2523352 n) (@lem2523393 n)). Qed.
Lemma lem2523395 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem2523396 (n : int) : (term180 n) = (term208 n).
Proof. exact (MK_COMB (@lem2523395) (@lem2523394 n)). Qed.
Lemma lem2523397 (n : int) : (term208 n) = (term207 n).
Proof. exact (@lem1982721 (term207 n)). Qed.
Lemma lem2523398 (n : int) : (term180 n) = (term207 n).
Proof. exact (TRANS (@lem2523396 n) (@lem2523397 n)). Qed.
Lemma lem2523400 (n : int) : (term179 n) = (term207 n).
Proof. exact (TRANS (@lem2523351 n) (@lem2523398 n)). Qed.
Lemma lem2523401 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523402 (n : int) : (term209 n) = (term210 n).
Proof. exact (MK_COMB (@lem2523401) (@lem2523400 n)). Qed.
Lemma lem2523403 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523404 (n : int) : (term178 n) = (term211 n).
Proof. exact (MK_COMB (@lem2523402 n) (@lem2523403)). Qed.
Lemma lem2523405 (n : int) : (term107 n) = (term211 n).
Proof. exact (TRANS (@lem2523339 n) (@lem2523404 n)). Qed.
Lemma lem2523406 (n : int) : (term120 n) = (term212 n).
Proof. exact (@lem1988287 (real_of_int n) term117). Qed.
Lemma lem2523413 : term117 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem2523416 (n : int) : (term213 n) = (term213 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2523417 (n : int) : (term214 n) = (term215 n).
Proof. exact (MK_COMB (@lem2523416 n) (@lem2523413)). Qed.
Lemma lem2523418 (n : int) : (term215 n) = (term216 n).
Proof. exact (@lem1982792 (real_of_int n) term99). Qed.
Lemma lem2523420 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523421 : term99 = term185.
Proof. exact (@lem2523420 term100). Qed.
Lemma lem2523423 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523424 : term183 = term188.
Proof. exact (@lem2523423 term100). Qed.
Lemma lem2523425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523426 : term189 = term190.
Proof. exact (MK_COMB (@lem2523425) (@lem2523424)). Qed.
Lemma lem2523427 : term191 = term192.
Proof. exact (MK_COMB (@lem2523426) (@lem2523421)). Qed.
Lemma lem2523428 : term192 = term193.
Proof. exact (@lem1981613 term183 term99 term99 term99). Qed.
Lemma lem2523430 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2523431 : term196 = term197.
Proof. exact (@lem2523430 term100 term100). Qed.
Lemma lem2523432 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523433 : term199 = term100.
Proof. exact (EQ_MP (@lem2523432) (@lem940073)). Qed.
Lemma lem2523434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523435 : term197 = term99.
Proof. exact (MK_COMB (@lem2523434) (@lem2523433)). Qed.
Lemma lem2523436 : term196 = term99.
Proof. exact (TRANS (@lem2523431) (@lem2523435)). Qed.
Lemma lem2523438 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523439 : term191 = term202.
Proof. exact (@lem2523438 term100 term100). Qed.
Lemma lem2523440 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523441 : term199 = term100.
Proof. exact (EQ_MP (@lem2523440) (@lem940073)). Qed.
Lemma lem2523442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523443 : term197 = term99.
Proof. exact (MK_COMB (@lem2523442) (@lem2523441)). Qed.
Lemma lem2523444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523445 : term202 = term183.
Proof. exact (MK_COMB (@lem2523444) (@lem2523443)). Qed.
Lemma lem2523446 : term191 = term183.
Proof. exact (TRANS (@lem2523439) (@lem2523445)). Qed.
Lemma lem2523447 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2523448 : term203 = term204.
Proof. exact (MK_COMB (@lem2523447) (@lem2523446)). Qed.
Lemma lem2523449 : term193 = term188.
Proof. exact (MK_COMB (@lem2523448) (@lem2523436)). Qed.
Lemma lem2523450 : term192 = term188.
Proof. exact (TRANS (@lem2523428) (@lem2523449)). Qed.
Lemma lem2523451 : term191 = term188.
Proof. exact (TRANS (@lem2523427) (@lem2523450)). Qed.
Lemma lem2523453 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2523454 : term188 = term183.
Proof. exact (@lem2523453 term183). Qed.
Lemma lem2523455 : term191 = term183.
Proof. exact (TRANS (@lem2523451) (@lem2523454)). Qed.
Lemma lem2523456 (n : int) : (term101 n) = (term101 n).
Proof. exact (eq_refl (term101 n)). Qed.
Lemma lem2523459 (n : int) : (term216 n) = (term217 n).
Proof. exact (MK_COMB (@lem2523456 n) (@lem2523455)). Qed.
Lemma lem2523460 (n : int) : (term215 n) = (term217 n).
Proof. exact (TRANS (@lem2523418 n) (@lem2523459 n)). Qed.
Lemma lem2523461 (n : int) : (term214 n) = (term217 n).
Proof. exact (TRANS (@lem2523417 n) (@lem2523460 n)). Qed.
Lemma lem2523462 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523463 (n : int) : (term218 n) = (term219 n).
Proof. exact (MK_COMB (@lem2523462) (@lem2523461 n)). Qed.
Lemma lem2523464 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523465 (n : int) : (term212 n) = (term220 n).
Proof. exact (MK_COMB (@lem2523463 n) (@lem2523464)). Qed.
Lemma lem2523466 (n : int) : (term120 n) = (term220 n).
Proof. exact (TRANS (@lem2523406 n) (@lem2523465 n)). Qed.
Lemma lem2523467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523468 (n : int) : (term109 n) = (term221 n).
Proof. exact (MK_COMB (@lem2523467) (@lem2523405 n)). Qed.
Lemma lem2523469 (n : int) : (term121 n) = (term222 n).
Proof. exact (MK_COMB (@lem2523468 n) (@lem2523466 n)). Qed.
Lemma lem2523470 (n : int) : (term139 n) = (term223 n).
Proof. exact (@lem1988287 (term138 n) term117). Qed.
Lemma lem2523477 : term117 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem2523478 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523485 (n : int) : (term135 n) = term106.
Proof. exact (@lem1982729 (real_of_int n)). Qed.
Lemma lem2523486 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523487 (n : int) : (term137 n) = term116.
Proof. exact (MK_COMB (@lem2523486) (@lem2523485 n)). Qed.
Lemma lem2523488 (n : int) : (term138 n) = term224.
Proof. exact (MK_COMB (@lem2523487 n) (@lem2523478)). Qed.
Lemma lem2523489 : term224 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2523490 (n : int) : (term138 n) = term106.
Proof. exact (TRANS (@lem2523488 n) (@lem2523489)). Qed.
Lemma lem2523491 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2523492 (n : int) : (term225 n) = term226.
Proof. exact (MK_COMB (@lem2523491) (@lem2523490 n)). Qed.
Lemma lem2523493 (n : int) : (term227 n) = term228.
Proof. exact (MK_COMB (@lem2523492 n) (@lem2523477)). Qed.
Lemma lem2523494 : term228 = term229.
Proof. exact (@lem1982792 term106 term99). Qed.
Lemma lem2523496 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523497 : term99 = term185.
Proof. exact (@lem2523496 term100). Qed.
Lemma lem2523499 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523500 : term183 = term188.
Proof. exact (@lem2523499 term100). Qed.
Lemma lem2523501 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523502 : term189 = term190.
Proof. exact (MK_COMB (@lem2523501) (@lem2523500)). Qed.
Lemma lem2523503 : term191 = term192.
Proof. exact (MK_COMB (@lem2523502) (@lem2523497)). Qed.
Lemma lem2523504 : term192 = term193.
Proof. exact (@lem1981613 term183 term99 term99 term99). Qed.
Lemma lem2523506 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2523507 : term196 = term197.
Proof. exact (@lem2523506 term100 term100). Qed.
Lemma lem2523508 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523509 : term199 = term100.
Proof. exact (EQ_MP (@lem2523508) (@lem940073)). Qed.
Lemma lem2523510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523511 : term197 = term99.
Proof. exact (MK_COMB (@lem2523510) (@lem2523509)). Qed.
Lemma lem2523512 : term196 = term99.
Proof. exact (TRANS (@lem2523507) (@lem2523511)). Qed.
Lemma lem2523514 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523515 : term191 = term202.
Proof. exact (@lem2523514 term100 term100). Qed.
Lemma lem2523516 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523517 : term199 = term100.
Proof. exact (EQ_MP (@lem2523516) (@lem940073)). Qed.
Lemma lem2523518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523519 : term197 = term99.
Proof. exact (MK_COMB (@lem2523518) (@lem2523517)). Qed.
Lemma lem2523520 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523521 : term202 = term183.
Proof. exact (MK_COMB (@lem2523520) (@lem2523519)). Qed.
Lemma lem2523522 : term191 = term183.
Proof. exact (TRANS (@lem2523515) (@lem2523521)). Qed.
Lemma lem2523523 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2523524 : term203 = term204.
Proof. exact (MK_COMB (@lem2523523) (@lem2523522)). Qed.
Lemma lem2523525 : term193 = term188.
Proof. exact (MK_COMB (@lem2523524) (@lem2523512)). Qed.
Lemma lem2523526 : term192 = term188.
Proof. exact (TRANS (@lem2523504) (@lem2523525)). Qed.
Lemma lem2523527 : term191 = term188.
Proof. exact (TRANS (@lem2523503) (@lem2523526)). Qed.
Lemma lem2523529 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2523530 : term188 = term183.
Proof. exact (@lem2523529 term183). Qed.
Lemma lem2523531 : term191 = term183.
Proof. exact (TRANS (@lem2523527) (@lem2523530)). Qed.
Lemma lem2523532 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem2523533 : term229 = term230.
Proof. exact (MK_COMB (@lem2523532) (@lem2523531)). Qed.
Lemma lem2523534 : term230 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2523535 : term229 = term183.
Proof. exact (TRANS (@lem2523533) (@lem2523534)). Qed.
Lemma lem2523536 : term228 = term183.
Proof. exact (TRANS (@lem2523494) (@lem2523535)). Qed.
Lemma lem2523537 (n : int) : (term227 n) = term183.
Proof. exact (TRANS (@lem2523493 n) (@lem2523536)). Qed.
Lemma lem2523538 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523539 (n : int) : (term231 n) = term232.
Proof. exact (MK_COMB (@lem2523538) (@lem2523537 n)). Qed.
Lemma lem2523540 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523541 (n : int) : (term223 n) = term233.
Proof. exact (MK_COMB (@lem2523539 n) (@lem2523540)). Qed.
Lemma lem2523542 (n : int) : (term139 n) = term233.
Proof. exact (TRANS (@lem2523470 n) (@lem2523541 n)). Qed.
Lemma lem2523543 (n : int) : (term152 n) = (term234 n).
Proof. exact (@lem1988287 term106 (term149 n)). Qed.
Lemma lem2523544 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2523545 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523552 (n : int) : (term135 n) = term106.
Proof. exact (@lem1982729 (real_of_int n)). Qed.
Lemma lem2523553 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523554 (n : int) : (term137 n) = term116.
Proof. exact (MK_COMB (@lem2523553) (@lem2523552 n)). Qed.
Lemma lem2523555 (n : int) : (term138 n) = term224.
Proof. exact (MK_COMB (@lem2523554 n) (@lem2523545)). Qed.
Lemma lem2523556 : term224 = term106.
Proof. exact (@lem1982721 term106). Qed.
Lemma lem2523557 (n : int) : (term138 n) = term106.
Proof. exact (TRANS (@lem2523555 n) (@lem2523556)). Qed.
Lemma lem2523558 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2523559 (n : int) : (term148 n) = term116.
Proof. exact (MK_COMB (@lem2523558) (@lem2523557 n)). Qed.
Lemma lem2523560 (n : int) : (term149 n) = term117.
Proof. exact (MK_COMB (@lem2523559 n) (@lem2523544)). Qed.
Lemma lem2523561 : term117 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem2523562 (n : int) : (term149 n) = term99.
Proof. exact (TRANS (@lem2523560 n) (@lem2523561)). Qed.
Lemma lem2523565 : term226 = term226.
Proof. exact (eq_refl term226). Qed.
Lemma lem2523566 (n : int) : (term235 n) = term228.
Proof. exact (MK_COMB (@lem2523565) (@lem2523562 n)). Qed.
Lemma lem2523567 : term228 = term229.
Proof. exact (@lem1982792 term106 term99). Qed.
Lemma lem2523569 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523570 : term99 = term185.
Proof. exact (@lem2523569 term100). Qed.
Lemma lem2523572 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523573 : term183 = term188.
Proof. exact (@lem2523572 term100). Qed.
Lemma lem2523574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523575 : term189 = term190.
Proof. exact (MK_COMB (@lem2523574) (@lem2523573)). Qed.
Lemma lem2523576 : term191 = term192.
Proof. exact (MK_COMB (@lem2523575) (@lem2523570)). Qed.
Lemma lem2523577 : term192 = term193.
Proof. exact (@lem1981613 term183 term99 term99 term99). Qed.
Lemma lem2523579 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2523580 : term196 = term197.
Proof. exact (@lem2523579 term100 term100). Qed.
Lemma lem2523581 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523582 : term199 = term100.
Proof. exact (EQ_MP (@lem2523581) (@lem940073)). Qed.
Lemma lem2523583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523584 : term197 = term99.
Proof. exact (MK_COMB (@lem2523583) (@lem2523582)). Qed.
Lemma lem2523585 : term196 = term99.
Proof. exact (TRANS (@lem2523580) (@lem2523584)). Qed.
Lemma lem2523587 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523588 : term191 = term202.
Proof. exact (@lem2523587 term100 term100). Qed.
Lemma lem2523589 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523590 : term199 = term100.
Proof. exact (EQ_MP (@lem2523589) (@lem940073)). Qed.
Lemma lem2523591 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523592 : term197 = term99.
Proof. exact (MK_COMB (@lem2523591) (@lem2523590)). Qed.
Lemma lem2523593 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523594 : term202 = term183.
Proof. exact (MK_COMB (@lem2523593) (@lem2523592)). Qed.
Lemma lem2523595 : term191 = term183.
Proof. exact (TRANS (@lem2523588) (@lem2523594)). Qed.
Lemma lem2523596 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2523597 : term203 = term204.
Proof. exact (MK_COMB (@lem2523596) (@lem2523595)). Qed.
Lemma lem2523598 : term193 = term188.
Proof. exact (MK_COMB (@lem2523597) (@lem2523585)). Qed.
Lemma lem2523599 : term192 = term188.
Proof. exact (TRANS (@lem2523577) (@lem2523598)). Qed.
Lemma lem2523600 : term191 = term188.
Proof. exact (TRANS (@lem2523576) (@lem2523599)). Qed.
Lemma lem2523602 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2523603 : term188 = term183.
Proof. exact (@lem2523602 term183). Qed.
Lemma lem2523604 : term191 = term183.
Proof. exact (TRANS (@lem2523600) (@lem2523603)). Qed.
Lemma lem2523605 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem2523606 : term229 = term230.
Proof. exact (MK_COMB (@lem2523605) (@lem2523604)). Qed.
Lemma lem2523607 : term230 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2523608 : term229 = term183.
Proof. exact (TRANS (@lem2523606) (@lem2523607)). Qed.
Lemma lem2523609 : term228 = term183.
Proof. exact (TRANS (@lem2523567) (@lem2523608)). Qed.
Lemma lem2523610 (n : int) : (term235 n) = term183.
Proof. exact (TRANS (@lem2523566 n) (@lem2523609)). Qed.
Lemma lem2523611 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523612 (n : int) : (term236 n) = term232.
Proof. exact (MK_COMB (@lem2523611) (@lem2523610 n)). Qed.
Lemma lem2523613 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523614 (n : int) : (term234 n) = term233.
Proof. exact (MK_COMB (@lem2523612 n) (@lem2523613)). Qed.
Lemma lem2523615 (n : int) : (term152 n) = term233.
Proof. exact (TRANS (@lem2523543 n) (@lem2523614 n)). Qed.
Lemma lem2523616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523617 (n : int) : (term141 n) = term237.
Proof. exact (MK_COMB (@lem2523616) (@lem2523542 n)). Qed.
Lemma lem2523618 (n : int) : (term153 n) = term238.
Proof. exact (MK_COMB (@lem2523617 n) (@lem2523615 n)). Qed.
Lemma lem2523619 : term159 = term239.
Proof. exact (@lem1988287 term106 term117). Qed.
Lemma lem2523626 : term117 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem2523629 : term226 = term226.
Proof. exact (eq_refl term226). Qed.
Lemma lem2523630 : term240 = term228.
Proof. exact (MK_COMB (@lem2523629) (@lem2523626)). Qed.
Lemma lem2523631 : term228 = term229.
Proof. exact (@lem1982792 term106 term99). Qed.
Lemma lem2523633 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523634 : term99 = term185.
Proof. exact (@lem2523633 term100). Qed.
Lemma lem2523636 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523637 : term183 = term188.
Proof. exact (@lem2523636 term100). Qed.
Lemma lem2523638 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2523639 : term189 = term190.
Proof. exact (MK_COMB (@lem2523638) (@lem2523637)). Qed.
Lemma lem2523640 : term191 = term192.
Proof. exact (MK_COMB (@lem2523639) (@lem2523634)). Qed.
Lemma lem2523641 : term192 = term193.
Proof. exact (@lem1981613 term183 term99 term99 term99). Qed.
Lemma lem2523643 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2523644 : term196 = term197.
Proof. exact (@lem2523643 term100 term100). Qed.
Lemma lem2523645 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523646 : term199 = term100.
Proof. exact (EQ_MP (@lem2523645) (@lem940073)). Qed.
Lemma lem2523647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523648 : term197 = term99.
Proof. exact (MK_COMB (@lem2523647) (@lem2523646)). Qed.
Lemma lem2523649 : term196 = term99.
Proof. exact (TRANS (@lem2523644) (@lem2523648)). Qed.
Lemma lem2523651 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523652 : term191 = term202.
Proof. exact (@lem2523651 term100 term100). Qed.
Lemma lem2523653 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523654 : term199 = term100.
Proof. exact (EQ_MP (@lem2523653) (@lem940073)). Qed.
Lemma lem2523655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523656 : term197 = term99.
Proof. exact (MK_COMB (@lem2523655) (@lem2523654)). Qed.
Lemma lem2523657 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523658 : term202 = term183.
Proof. exact (MK_COMB (@lem2523657) (@lem2523656)). Qed.
Lemma lem2523659 : term191 = term183.
Proof. exact (TRANS (@lem2523652) (@lem2523658)). Qed.
Lemma lem2523660 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2523661 : term203 = term204.
Proof. exact (MK_COMB (@lem2523660) (@lem2523659)). Qed.
Lemma lem2523662 : term193 = term188.
Proof. exact (MK_COMB (@lem2523661) (@lem2523649)). Qed.
Lemma lem2523663 : term192 = term188.
Proof. exact (TRANS (@lem2523641) (@lem2523662)). Qed.
Lemma lem2523664 : term191 = term188.
Proof. exact (TRANS (@lem2523640) (@lem2523663)). Qed.
Lemma lem2523666 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2523667 : term188 = term183.
Proof. exact (@lem2523666 term183). Qed.
Lemma lem2523668 : term191 = term183.
Proof. exact (TRANS (@lem2523664) (@lem2523667)). Qed.
Lemma lem2523669 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem2523670 : term229 = term230.
Proof. exact (MK_COMB (@lem2523669) (@lem2523668)). Qed.
Lemma lem2523671 : term230 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2523672 : term229 = term183.
Proof. exact (TRANS (@lem2523670) (@lem2523671)). Qed.
Lemma lem2523673 : term228 = term183.
Proof. exact (TRANS (@lem2523631) (@lem2523672)). Qed.
Lemma lem2523674 : term240 = term183.
Proof. exact (TRANS (@lem2523630) (@lem2523673)). Qed.
Lemma lem2523675 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523676 : term241 = term232.
Proof. exact (MK_COMB (@lem2523675) (@lem2523674)). Qed.
Lemma lem2523677 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523678 : term239 = term233.
Proof. exact (MK_COMB (@lem2523676) (@lem2523677)). Qed.
Lemma lem2523679 : term159 = term233.
Proof. exact (TRANS (@lem2523619) (@lem2523678)). Qed.
Lemma lem2523680 (n : int) : (term168 n) = (term242 n).
Proof. exact (@lem1988287 term106 (term165 n)). Qed.
Lemma lem2523688 (n : int) : (term243 n) = (term244 n).
Proof. exact (@lem1982792 term106 (term165 n)). Qed.
Lemma lem2523693 (n : int) : (term244 n) = (term245 n).
Proof. exact (@lem1982721 (term245 n)). Qed.
Lemma lem2523695 (n : int) : (term243 n) = (term245 n).
Proof. exact (TRANS (@lem2523688 n) (@lem2523693 n)). Qed.
Lemma lem2523696 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523697 (n : int) : (term246 n) = (term247 n).
Proof. exact (MK_COMB (@lem2523696) (@lem2523695 n)). Qed.
Lemma lem2523698 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523699 (n : int) : (term242 n) = (term248 n).
Proof. exact (MK_COMB (@lem2523697 n) (@lem2523698)). Qed.
Lemma lem2523700 (n : int) : (term168 n) = (term248 n).
Proof. exact (TRANS (@lem2523680 n) (@lem2523699 n)). Qed.
Lemma lem2523701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523702 : term170 = term237.
Proof. exact (MK_COMB (@lem2523701) (@lem2523679)). Qed.
Lemma lem2523703 (n : int) : (term171 n) = (term249 n).
Proof. exact (MK_COMB (@lem2523702) (@lem2523700 n)). Qed.
Lemma lem2523704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523705 (n : int) : (term172 n) = term250.
Proof. exact (MK_COMB (@lem2523704) (@lem2523618 n)). Qed.
Lemma lem2523706 (n : int) : (term173 n) = (term251 n).
Proof. exact (MK_COMB (@lem2523705 n) (@lem2523703 n)). Qed.
Lemma lem2523707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2523708 (n : int) : (term174 n) = (term252 n).
Proof. exact (MK_COMB (@lem2523707) (@lem2523469 n)). Qed.
Lemma lem2523709 (n : int) : (term175 n) = (term253 n).
Proof. exact (MK_COMB (@lem2523708 n) (@lem2523706 n)). Qed.
Lemma lem2523716 (n : int) : (term177 n) = (term253 n).
Proof. exact (TRANS (@lem2523338 n) (@lem2523709 n)). Qed.
Lemma lem2523738 (n : int) : (term253 n) = (term254 n).
Proof. exact (@lem19158 term238 (term222 n) (term249 n)). Qed.
Lemma lem2523739 (n : int) : (term255 n) = (term256 n).
Proof. exact (@lem19158 term233 (term222 n) (term248 n)). Qed.
Lemma lem2523746 (n : int) : (term257 n) = (term258 n).
Proof. exact (@lem19367 (term211 n) (term220 n) (term248 n)). Qed.
Lemma lem2523753 (n : int) : (term259 n) = (term260 n).
Proof. exact (@lem19367 (term211 n) (term220 n) term233). Qed.
Lemma lem2523754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523755 (n : int) : (term261 n) = (term262 n).
Proof. exact (MK_COMB (@lem2523754) (@lem2523753 n)). Qed.
Lemma lem2523756 (n : int) : (term256 n) = (term263 n).
Proof. exact (MK_COMB (@lem2523755 n) (@lem2523746 n)). Qed.
Lemma lem2523757 (n : int) : (term255 n) = (term263 n).
Proof. exact (TRANS (@lem2523739 n) (@lem2523756 n)). Qed.
Lemma lem2523758 (n : int) : (term264 n) = (term265 n).
Proof. exact (@lem19158 term233 (term222 n) term233). Qed.
Lemma lem2523765 (n : int) : (term259 n) = (term260 n).
Proof. exact (@lem19367 (term211 n) (term220 n) term233). Qed.
Lemma lem2523772 (n : int) : (term259 n) = (term260 n).
Proof. exact (@lem19367 (term211 n) (term220 n) term233). Qed.
Lemma lem2523773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523774 (n : int) : (term261 n) = (term262 n).
Proof. exact (MK_COMB (@lem2523773) (@lem2523772 n)). Qed.
Lemma lem2523775 (n : int) : (term265 n) = (term266 n).
Proof. exact (MK_COMB (@lem2523774 n) (@lem2523765 n)). Qed.
Lemma lem2523776 (n : int) : (term264 n) = (term266 n).
Proof. exact (TRANS (@lem2523758 n) (@lem2523775 n)). Qed.
Lemma lem2523777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523778 (n : int) : (term267 n) = (term268 n).
Proof. exact (MK_COMB (@lem2523777) (@lem2523776 n)). Qed.
Lemma lem2523779 (n : int) : (term254 n) = (term269 n).
Proof. exact (MK_COMB (@lem2523778 n) (@lem2523757 n)). Qed.
Lemma lem2523781 (n : int) : (term253 n) = (term269 n).
Proof. exact (TRANS (@lem2523738 n) (@lem2523779 n)). Qed.
Lemma lem2523782 (n : int) : (term177 n) = (term269 n).
Proof. exact (TRANS (@lem2523716 n) (@lem2523781 n)). Qed.
Lemma lem2523814 (x : real) (r : real) : (term270 x r) = (term271 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2523815 (n : int) : (term248 n) = (term272 n).
Proof. exact (@lem2523814 (real_of_int n) term106). Qed.
Lemma lem2523822 (n : int) : (term273 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2523823 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523824 (n : int) : (term274 n) = (term275 n).
Proof. exact (MK_COMB (@lem2523823) (@lem2523822 n)). Qed.
Lemma lem2523825 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523826 (n : int) : (term276 n) = (term277 n).
Proof. exact (MK_COMB (@lem2523824 n) (@lem2523825)). Qed.
Lemma lem2523839 (n : int) : (term278 n) = (term278 n).
Proof. exact (eq_refl (term278 n)). Qed.
Lemma lem2523840 (n : int) : (term272 n) = (term279 n).
Proof. exact (MK_COMB (@lem2523839 n) (@lem2523826 n)). Qed.
Lemma lem2523841 (n : int) : (term248 n) = (term279 n).
Proof. exact (TRANS (@lem2523815 n) (@lem2523840 n)). Qed.
Lemma lem2523842 (n : int) : (term280 n) = (term280 n).
Proof. exact (eq_refl (term280 n)). Qed.
Lemma lem2523845 (n : int) : (term281 n) = (term282 n).
Proof. exact (MK_COMB (@lem2523842 n) (@lem2523841 n)). Qed.
Lemma lem2523847 (x : real) (r : real) : (term270 x r) = (term271 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2523848 (n : int) : (term248 n) = (term272 n).
Proof. exact (@lem2523847 (real_of_int n) term106). Qed.
Lemma lem2523855 (n : int) : (term273 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2523856 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2523857 (n : int) : (term274 n) = (term275 n).
Proof. exact (MK_COMB (@lem2523856) (@lem2523855 n)). Qed.
Lemma lem2523858 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2523859 (n : int) : (term276 n) = (term277 n).
Proof. exact (MK_COMB (@lem2523857 n) (@lem2523858)). Qed.
Lemma lem2523872 (n : int) : (term278 n) = (term278 n).
Proof. exact (eq_refl (term278 n)). Qed.
Lemma lem2523873 (n : int) : (term272 n) = (term279 n).
Proof. exact (MK_COMB (@lem2523872 n) (@lem2523859 n)). Qed.
Lemma lem2523874 (n : int) : (term248 n) = (term279 n).
Proof. exact (TRANS (@lem2523848 n) (@lem2523873 n)). Qed.
Lemma lem2523875 (n : int) : (term283 n) = (term283 n).
Proof. exact (eq_refl (term283 n)). Qed.
Lemma lem2523878 (n : int) : (term284 n) = (term285 n).
Proof. exact (MK_COMB (@lem2523875 n) (@lem2523874 n)). Qed.
Lemma lem2523879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2523880 (n : int) : (term286 n) = (term287 n).
Proof. exact (MK_COMB (@lem2523879) (@lem2523845 n)). Qed.
Lemma lem2523881 (n : int) : (term258 n) = (term288 n).
Proof. exact (MK_COMB (@lem2523880 n) (@lem2523878 n)). Qed.
Lemma lem2523883 (n : int) : (term262 n) = (term262 n).
Proof. exact (eq_refl (term262 n)). Qed.
Lemma lem2523884 (n : int) : (term263 n) = (term289 n).
Proof. exact (MK_COMB (@lem2523883 n) (@lem2523881 n)). Qed.
Lemma lem2523886 (n : int) : (term268 n) = (term268 n).
Proof. exact (eq_refl (term268 n)). Qed.
Lemma lem2523887 (n : int) : (term269 n) = (term290 n).
Proof. exact (MK_COMB (@lem2523886 n) (@lem2523884 n)). Qed.
Lemma lem2523888 (n : int) (h1 : term290 n) : term290 n.
Proof. exact (h1). Qed.
Lemma lem2523889 (n : int) (h1 : term266 n) : term266 n.
Proof. exact (h1). Qed.
Lemma lem2523890 (n : int) (h1 : term260 n) : term260 n.
Proof. exact (h1). Qed.
Lemma lem2523891 (n : int) (h1 : term291 n) : term291 n.
Proof. exact (h1). Qed.
Lemma lem2523892 (n : int) (h1 : term291 n) : term233.
Proof. exact (proj2 (@lem2523891 n h1)). Qed.
Lemma lem2523895 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2523896 : term233 = term292.
Proof. exact (@lem2523895 term106 term183). Qed.
Lemma lem2523898 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523899 : term183 = term188.
Proof. exact (@lem2523898 term100). Qed.
Lemma lem2523901 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523902 : term106 = term293.
Proof. exact (@lem2523901 (NUMERAL 0)). Qed.
Lemma lem2523903 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523904 : term294 = term295.
Proof. exact (MK_COMB (@lem2523903) (@lem2523902)). Qed.
Lemma lem2523905 : term292 = term296.
Proof. exact (MK_COMB (@lem2523904) (@lem2523899)). Qed.
Lemma lem2523906 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2523908 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2523909 : term299 = term300.
Proof. exact (@lem2523908 (NUMERAL 0) term100). Qed.
Lemma lem2523910 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2523911 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2523912 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2523911 h1) (fun h1 : term300 = True => @lem2523910)). Qed.
Lemma lem2523913 : term300 = True.
Proof. exact (EQ_MP (@lem2523912) (@lem2523910)). Qed.
Lemma lem2523914 : term299 = True.
Proof. exact (TRANS (@lem2523909) (@lem2523913)). Qed.
Lemma lem2523915 : True = term299.
Proof. exact (SYM (@lem2523914)). Qed.
Lemma lem2523916 : term299.
Proof. exact (EQ_MP (@lem2523915) (@lem0)). Qed.
Lemma lem2523917 : term302.
Proof. exact (@lem2523906 (@lem2523916)). Qed.
Lemma lem2523919 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2523920 : term299 = term300.
Proof. exact (@lem2523919 (NUMERAL 0) term100). Qed.
Lemma lem2523921 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2523922 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2523923 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2523922 h1) (fun h1 : term300 = True => @lem2523921)). Qed.
Lemma lem2523924 : term300 = True.
Proof. exact (EQ_MP (@lem2523923) (@lem2523921)). Qed.
Lemma lem2523925 : term299 = True.
Proof. exact (TRANS (@lem2523920) (@lem2523924)). Qed.
Lemma lem2523926 : True = term299.
Proof. exact (SYM (@lem2523925)). Qed.
Lemma lem2523927 : term299.
Proof. exact (EQ_MP (@lem2523926) (@lem0)). Qed.
Lemma lem2523928 : term296 = term303.
Proof. exact (@lem2523917 (@lem2523927)). Qed.
Lemma lem2523930 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2523931 : term191 = term202.
Proof. exact (@lem2523930 term100 term100). Qed.
Lemma lem2523932 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2523933 : term199 = term100.
Proof. exact (EQ_MP (@lem2523932) (@lem940073)). Qed.
Lemma lem2523934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2523935 : term197 = term99.
Proof. exact (MK_COMB (@lem2523934) (@lem2523933)). Qed.
Lemma lem2523936 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2523937 : term202 = term183.
Proof. exact (MK_COMB (@lem2523936) (@lem2523935)). Qed.
Lemma lem2523938 : term191 = term183.
Proof. exact (TRANS (@lem2523931) (@lem2523937)). Qed.
Lemma lem2523940 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2523941 : term305 = term106.
Proof. exact (@lem2523940 term100). Qed.
Lemma lem2523942 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523943 : term306 = term294.
Proof. exact (MK_COMB (@lem2523942) (@lem2523941)). Qed.
Lemma lem2523944 : term303 = term292.
Proof. exact (MK_COMB (@lem2523943) (@lem2523938)). Qed.
Lemma lem2523946 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2523947 : term292 = term309.
Proof. exact (@lem2523946 (NUMERAL 0) term100). Qed.
Lemma lem2523948 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2523949 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2523950 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2523949 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2523948)). Qed.
Lemma lem2523951 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2523950) (@lem2523948)). Qed.
Lemma lem2523952 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2523953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2523954 : term310 = (and True).
Proof. exact (MK_COMB (@lem2523953) (@lem2523952)). Qed.
Lemma lem2523955 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2523954) (@lem2523951)). Qed.
Lemma lem2523957 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2523958 : term309 = False.
Proof. exact (TRANS (@lem2523955) (@lem2523957)). Qed.
Lemma lem2523959 : term292 = False.
Proof. exact (TRANS (@lem2523947) (@lem2523958)). Qed.
Lemma lem2523960 : term303 = False.
Proof. exact (TRANS (@lem2523944) (@lem2523959)). Qed.
Lemma lem2523961 : term296 = False.
Proof. exact (TRANS (@lem2523928) (@lem2523960)). Qed.
Lemma lem2523962 : term292 = False.
Proof. exact (TRANS (@lem2523905) (@lem2523961)). Qed.
Lemma lem2523963 : term233 = False.
Proof. exact (TRANS (@lem2523896) (@lem2523962)). Qed.
Lemma lem2523964 (n : int) (h1 : term291 n) : False.
Proof. exact (EQ_MP (@lem2523963) (@lem2523892 n h1)). Qed.
Lemma lem2523965 (n : int) (h1 : term311 n) : term311 n.
Proof. exact (h1). Qed.
Lemma lem2523966 (n : int) (h1 : term311 n) : term233.
Proof. exact (proj2 (@lem2523965 n h1)). Qed.
Lemma lem2523969 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2523970 : term233 = term292.
Proof. exact (@lem2523969 term106 term183). Qed.
Lemma lem2523972 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2523973 : term183 = term188.
Proof. exact (@lem2523972 term100). Qed.
Lemma lem2523975 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2523976 : term106 = term293.
Proof. exact (@lem2523975 (NUMERAL 0)). Qed.
Lemma lem2523977 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2523978 : term294 = term295.
Proof. exact (MK_COMB (@lem2523977) (@lem2523976)). Qed.
Lemma lem2523979 : term292 = term296.
Proof. exact (MK_COMB (@lem2523978) (@lem2523973)). Qed.
Lemma lem2523980 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2523982 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2523983 : term299 = term300.
Proof. exact (@lem2523982 (NUMERAL 0) term100). Qed.
Lemma lem2523984 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2523985 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2523986 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2523985 h1) (fun h1 : term300 = True => @lem2523984)). Qed.
Lemma lem2523987 : term300 = True.
Proof. exact (EQ_MP (@lem2523986) (@lem2523984)). Qed.
Lemma lem2523988 : term299 = True.
Proof. exact (TRANS (@lem2523983) (@lem2523987)). Qed.
Lemma lem2523989 : True = term299.
Proof. exact (SYM (@lem2523988)). Qed.
Lemma lem2523990 : term299.
Proof. exact (EQ_MP (@lem2523989) (@lem0)). Qed.
Lemma lem2523991 : term302.
Proof. exact (@lem2523980 (@lem2523990)). Qed.
Lemma lem2523993 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2523994 : term299 = term300.
Proof. exact (@lem2523993 (NUMERAL 0) term100). Qed.
Lemma lem2523995 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2523996 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2523997 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2523996 h1) (fun h1 : term300 = True => @lem2523995)). Qed.
Lemma lem2523998 : term300 = True.
Proof. exact (EQ_MP (@lem2523997) (@lem2523995)). Qed.
Lemma lem2523999 : term299 = True.
Proof. exact (TRANS (@lem2523994) (@lem2523998)). Qed.
Lemma lem2524000 : True = term299.
Proof. exact (SYM (@lem2523999)). Qed.
Lemma lem2524001 : term299.
Proof. exact (EQ_MP (@lem2524000) (@lem0)). Qed.
Lemma lem2524002 : term296 = term303.
Proof. exact (@lem2523991 (@lem2524001)). Qed.
Lemma lem2524004 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524005 : term191 = term202.
Proof. exact (@lem2524004 term100 term100). Qed.
Lemma lem2524006 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524007 : term199 = term100.
Proof. exact (EQ_MP (@lem2524006) (@lem940073)). Qed.
Lemma lem2524008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524009 : term197 = term99.
Proof. exact (MK_COMB (@lem2524008) (@lem2524007)). Qed.
Lemma lem2524010 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524011 : term202 = term183.
Proof. exact (MK_COMB (@lem2524010) (@lem2524009)). Qed.
Lemma lem2524012 : term191 = term183.
Proof. exact (TRANS (@lem2524005) (@lem2524011)). Qed.
Lemma lem2524014 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524015 : term305 = term106.
Proof. exact (@lem2524014 term100). Qed.
Lemma lem2524016 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524017 : term306 = term294.
Proof. exact (MK_COMB (@lem2524016) (@lem2524015)). Qed.
Lemma lem2524018 : term303 = term292.
Proof. exact (MK_COMB (@lem2524017) (@lem2524012)). Qed.
Lemma lem2524020 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524021 : term292 = term309.
Proof. exact (@lem2524020 (NUMERAL 0) term100). Qed.
Lemma lem2524022 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524023 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524024 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524023 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524022)). Qed.
Lemma lem2524025 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524024) (@lem2524022)). Qed.
Lemma lem2524026 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524028 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524027) (@lem2524026)). Qed.
Lemma lem2524029 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524028) (@lem2524025)). Qed.
Lemma lem2524031 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524032 : term309 = False.
Proof. exact (TRANS (@lem2524029) (@lem2524031)). Qed.
Lemma lem2524033 : term292 = False.
Proof. exact (TRANS (@lem2524021) (@lem2524032)). Qed.
Lemma lem2524034 : term303 = False.
Proof. exact (TRANS (@lem2524018) (@lem2524033)). Qed.
Lemma lem2524035 : term296 = False.
Proof. exact (TRANS (@lem2524002) (@lem2524034)). Qed.
Lemma lem2524036 : term292 = False.
Proof. exact (TRANS (@lem2523979) (@lem2524035)). Qed.
Lemma lem2524037 : term233 = False.
Proof. exact (TRANS (@lem2523970) (@lem2524036)). Qed.
Lemma lem2524038 (n : int) (h1 : term311 n) : False.
Proof. exact (EQ_MP (@lem2524037) (@lem2523966 n h1)). Qed.
Lemma lem2524039 (n : int) (h1 : term260 n) : False.
Proof. exact (or_elim (@lem2523890 n h1) (fun h0 : term291 n => @lem2523964 n h0) (fun h0 : term311 n => @lem2524038 n h0)). Qed.
Lemma lem2524040 (n : int) (h1 : term260 n) : term260 n.
Proof. exact (h1). Qed.
Lemma lem2524041 (n : int) (h1 : term291 n) : term291 n.
Proof. exact (h1). Qed.
Lemma lem2524042 (n : int) (h1 : term291 n) : term233.
Proof. exact (proj2 (@lem2524041 n h1)). Qed.
Lemma lem2524045 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524046 : term233 = term292.
Proof. exact (@lem2524045 term106 term183). Qed.
Lemma lem2524048 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524049 : term183 = term188.
Proof. exact (@lem2524048 term100). Qed.
Lemma lem2524051 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524052 : term106 = term293.
Proof. exact (@lem2524051 (NUMERAL 0)). Qed.
Lemma lem2524053 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524054 : term294 = term295.
Proof. exact (MK_COMB (@lem2524053) (@lem2524052)). Qed.
Lemma lem2524055 : term292 = term296.
Proof. exact (MK_COMB (@lem2524054) (@lem2524049)). Qed.
Lemma lem2524056 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524058 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524059 : term299 = term300.
Proof. exact (@lem2524058 (NUMERAL 0) term100). Qed.
Lemma lem2524060 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524061 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524062 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524061 h1) (fun h1 : term300 = True => @lem2524060)). Qed.
Lemma lem2524063 : term300 = True.
Proof. exact (EQ_MP (@lem2524062) (@lem2524060)). Qed.
Lemma lem2524064 : term299 = True.
Proof. exact (TRANS (@lem2524059) (@lem2524063)). Qed.
Lemma lem2524065 : True = term299.
Proof. exact (SYM (@lem2524064)). Qed.
Lemma lem2524066 : term299.
Proof. exact (EQ_MP (@lem2524065) (@lem0)). Qed.
Lemma lem2524067 : term302.
Proof. exact (@lem2524056 (@lem2524066)). Qed.
Lemma lem2524069 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524070 : term299 = term300.
Proof. exact (@lem2524069 (NUMERAL 0) term100). Qed.
Lemma lem2524071 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524072 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524073 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524072 h1) (fun h1 : term300 = True => @lem2524071)). Qed.
Lemma lem2524074 : term300 = True.
Proof. exact (EQ_MP (@lem2524073) (@lem2524071)). Qed.
Lemma lem2524075 : term299 = True.
Proof. exact (TRANS (@lem2524070) (@lem2524074)). Qed.
Lemma lem2524076 : True = term299.
Proof. exact (SYM (@lem2524075)). Qed.
Lemma lem2524077 : term299.
Proof. exact (EQ_MP (@lem2524076) (@lem0)). Qed.
Lemma lem2524078 : term296 = term303.
Proof. exact (@lem2524067 (@lem2524077)). Qed.
Lemma lem2524080 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524081 : term191 = term202.
Proof. exact (@lem2524080 term100 term100). Qed.
Lemma lem2524082 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524083 : term199 = term100.
Proof. exact (EQ_MP (@lem2524082) (@lem940073)). Qed.
Lemma lem2524084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524085 : term197 = term99.
Proof. exact (MK_COMB (@lem2524084) (@lem2524083)). Qed.
Lemma lem2524086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524087 : term202 = term183.
Proof. exact (MK_COMB (@lem2524086) (@lem2524085)). Qed.
Lemma lem2524088 : term191 = term183.
Proof. exact (TRANS (@lem2524081) (@lem2524087)). Qed.
Lemma lem2524090 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524091 : term305 = term106.
Proof. exact (@lem2524090 term100). Qed.
Lemma lem2524092 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524093 : term306 = term294.
Proof. exact (MK_COMB (@lem2524092) (@lem2524091)). Qed.
Lemma lem2524094 : term303 = term292.
Proof. exact (MK_COMB (@lem2524093) (@lem2524088)). Qed.
Lemma lem2524096 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524097 : term292 = term309.
Proof. exact (@lem2524096 (NUMERAL 0) term100). Qed.
Lemma lem2524098 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524099 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524100 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524099 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524098)). Qed.
Lemma lem2524101 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524100) (@lem2524098)). Qed.
Lemma lem2524102 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524104 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524103) (@lem2524102)). Qed.
Lemma lem2524105 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524104) (@lem2524101)). Qed.
Lemma lem2524107 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524108 : term309 = False.
Proof. exact (TRANS (@lem2524105) (@lem2524107)). Qed.
Lemma lem2524109 : term292 = False.
Proof. exact (TRANS (@lem2524097) (@lem2524108)). Qed.
Lemma lem2524110 : term303 = False.
Proof. exact (TRANS (@lem2524094) (@lem2524109)). Qed.
Lemma lem2524111 : term296 = False.
Proof. exact (TRANS (@lem2524078) (@lem2524110)). Qed.
Lemma lem2524112 : term292 = False.
Proof. exact (TRANS (@lem2524055) (@lem2524111)). Qed.
Lemma lem2524113 : term233 = False.
Proof. exact (TRANS (@lem2524046) (@lem2524112)). Qed.
Lemma lem2524114 (n : int) (h1 : term291 n) : False.
Proof. exact (EQ_MP (@lem2524113) (@lem2524042 n h1)). Qed.
Lemma lem2524115 (n : int) (h1 : term311 n) : term311 n.
Proof. exact (h1). Qed.
Lemma lem2524116 (n : int) (h1 : term311 n) : term233.
Proof. exact (proj2 (@lem2524115 n h1)). Qed.
Lemma lem2524119 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524120 : term233 = term292.
Proof. exact (@lem2524119 term106 term183). Qed.
Lemma lem2524122 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524123 : term183 = term188.
Proof. exact (@lem2524122 term100). Qed.
Lemma lem2524125 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524126 : term106 = term293.
Proof. exact (@lem2524125 (NUMERAL 0)). Qed.
Lemma lem2524127 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524128 : term294 = term295.
Proof. exact (MK_COMB (@lem2524127) (@lem2524126)). Qed.
Lemma lem2524129 : term292 = term296.
Proof. exact (MK_COMB (@lem2524128) (@lem2524123)). Qed.
Lemma lem2524130 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524132 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524133 : term299 = term300.
Proof. exact (@lem2524132 (NUMERAL 0) term100). Qed.
Lemma lem2524134 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524135 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524136 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524135 h1) (fun h1 : term300 = True => @lem2524134)). Qed.
Lemma lem2524137 : term300 = True.
Proof. exact (EQ_MP (@lem2524136) (@lem2524134)). Qed.
Lemma lem2524138 : term299 = True.
Proof. exact (TRANS (@lem2524133) (@lem2524137)). Qed.
Lemma lem2524139 : True = term299.
Proof. exact (SYM (@lem2524138)). Qed.
Lemma lem2524140 : term299.
Proof. exact (EQ_MP (@lem2524139) (@lem0)). Qed.
Lemma lem2524141 : term302.
Proof. exact (@lem2524130 (@lem2524140)). Qed.
Lemma lem2524143 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524144 : term299 = term300.
Proof. exact (@lem2524143 (NUMERAL 0) term100). Qed.
Lemma lem2524145 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524146 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524147 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524146 h1) (fun h1 : term300 = True => @lem2524145)). Qed.
Lemma lem2524148 : term300 = True.
Proof. exact (EQ_MP (@lem2524147) (@lem2524145)). Qed.
Lemma lem2524149 : term299 = True.
Proof. exact (TRANS (@lem2524144) (@lem2524148)). Qed.
Lemma lem2524150 : True = term299.
Proof. exact (SYM (@lem2524149)). Qed.
Lemma lem2524151 : term299.
Proof. exact (EQ_MP (@lem2524150) (@lem0)). Qed.
Lemma lem2524152 : term296 = term303.
Proof. exact (@lem2524141 (@lem2524151)). Qed.
Lemma lem2524154 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524155 : term191 = term202.
Proof. exact (@lem2524154 term100 term100). Qed.
Lemma lem2524156 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524157 : term199 = term100.
Proof. exact (EQ_MP (@lem2524156) (@lem940073)). Qed.
Lemma lem2524158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524159 : term197 = term99.
Proof. exact (MK_COMB (@lem2524158) (@lem2524157)). Qed.
Lemma lem2524160 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524161 : term202 = term183.
Proof. exact (MK_COMB (@lem2524160) (@lem2524159)). Qed.
Lemma lem2524162 : term191 = term183.
Proof. exact (TRANS (@lem2524155) (@lem2524161)). Qed.
Lemma lem2524164 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524165 : term305 = term106.
Proof. exact (@lem2524164 term100). Qed.
Lemma lem2524166 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524167 : term306 = term294.
Proof. exact (MK_COMB (@lem2524166) (@lem2524165)). Qed.
Lemma lem2524168 : term303 = term292.
Proof. exact (MK_COMB (@lem2524167) (@lem2524162)). Qed.
Lemma lem2524170 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524171 : term292 = term309.
Proof. exact (@lem2524170 (NUMERAL 0) term100). Qed.
Lemma lem2524172 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524173 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524174 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524173 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524172)). Qed.
Lemma lem2524175 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524174) (@lem2524172)). Qed.
Lemma lem2524176 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524178 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524177) (@lem2524176)). Qed.
Lemma lem2524179 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524178) (@lem2524175)). Qed.
Lemma lem2524181 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524182 : term309 = False.
Proof. exact (TRANS (@lem2524179) (@lem2524181)). Qed.
Lemma lem2524183 : term292 = False.
Proof. exact (TRANS (@lem2524171) (@lem2524182)). Qed.
Lemma lem2524184 : term303 = False.
Proof. exact (TRANS (@lem2524168) (@lem2524183)). Qed.
Lemma lem2524185 : term296 = False.
Proof. exact (TRANS (@lem2524152) (@lem2524184)). Qed.
Lemma lem2524186 : term292 = False.
Proof. exact (TRANS (@lem2524129) (@lem2524185)). Qed.
Lemma lem2524187 : term233 = False.
Proof. exact (TRANS (@lem2524120) (@lem2524186)). Qed.
Lemma lem2524188 (n : int) (h1 : term311 n) : False.
Proof. exact (EQ_MP (@lem2524187) (@lem2524116 n h1)). Qed.
Lemma lem2524189 (n : int) (h1 : term260 n) : False.
Proof. exact (or_elim (@lem2524040 n h1) (fun h0 : term291 n => @lem2524114 n h0) (fun h0 : term311 n => @lem2524188 n h0)). Qed.
Lemma lem2524190 (n : int) (h1 : term266 n) : False.
Proof. exact (or_elim (@lem2523889 n h1) (fun h0 : term260 n => @lem2524039 n h0) (fun h0 : term260 n => @lem2524189 n h0)). Qed.
Lemma lem2524191 (n : int) (h1 : term289 n) : term289 n.
Proof. exact (h1). Qed.
Lemma lem2524192 (n : int) (h1 : term260 n) : term260 n.
Proof. exact (h1). Qed.
Lemma lem2524193 (n : int) (h1 : term291 n) : term291 n.
Proof. exact (h1). Qed.
Lemma lem2524194 (n : int) (h1 : term291 n) : term233.
Proof. exact (proj2 (@lem2524193 n h1)). Qed.
Lemma lem2524197 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524198 : term233 = term292.
Proof. exact (@lem2524197 term106 term183). Qed.
Lemma lem2524200 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524201 : term183 = term188.
Proof. exact (@lem2524200 term100). Qed.
Lemma lem2524203 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524204 : term106 = term293.
Proof. exact (@lem2524203 (NUMERAL 0)). Qed.
Lemma lem2524205 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524206 : term294 = term295.
Proof. exact (MK_COMB (@lem2524205) (@lem2524204)). Qed.
Lemma lem2524207 : term292 = term296.
Proof. exact (MK_COMB (@lem2524206) (@lem2524201)). Qed.
Lemma lem2524208 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524210 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524211 : term299 = term300.
Proof. exact (@lem2524210 (NUMERAL 0) term100). Qed.
Lemma lem2524212 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524213 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524214 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524213 h1) (fun h1 : term300 = True => @lem2524212)). Qed.
Lemma lem2524215 : term300 = True.
Proof. exact (EQ_MP (@lem2524214) (@lem2524212)). Qed.
Lemma lem2524216 : term299 = True.
Proof. exact (TRANS (@lem2524211) (@lem2524215)). Qed.
Lemma lem2524217 : True = term299.
Proof. exact (SYM (@lem2524216)). Qed.
Lemma lem2524218 : term299.
Proof. exact (EQ_MP (@lem2524217) (@lem0)). Qed.
Lemma lem2524219 : term302.
Proof. exact (@lem2524208 (@lem2524218)). Qed.
Lemma lem2524221 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524222 : term299 = term300.
Proof. exact (@lem2524221 (NUMERAL 0) term100). Qed.
Lemma lem2524223 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524224 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524225 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524224 h1) (fun h1 : term300 = True => @lem2524223)). Qed.
Lemma lem2524226 : term300 = True.
Proof. exact (EQ_MP (@lem2524225) (@lem2524223)). Qed.
Lemma lem2524227 : term299 = True.
Proof. exact (TRANS (@lem2524222) (@lem2524226)). Qed.
Lemma lem2524228 : True = term299.
Proof. exact (SYM (@lem2524227)). Qed.
Lemma lem2524229 : term299.
Proof. exact (EQ_MP (@lem2524228) (@lem0)). Qed.
Lemma lem2524230 : term296 = term303.
Proof. exact (@lem2524219 (@lem2524229)). Qed.
Lemma lem2524232 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524233 : term191 = term202.
Proof. exact (@lem2524232 term100 term100). Qed.
Lemma lem2524234 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524235 : term199 = term100.
Proof. exact (EQ_MP (@lem2524234) (@lem940073)). Qed.
Lemma lem2524236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524237 : term197 = term99.
Proof. exact (MK_COMB (@lem2524236) (@lem2524235)). Qed.
Lemma lem2524238 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524239 : term202 = term183.
Proof. exact (MK_COMB (@lem2524238) (@lem2524237)). Qed.
Lemma lem2524240 : term191 = term183.
Proof. exact (TRANS (@lem2524233) (@lem2524239)). Qed.
Lemma lem2524242 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524243 : term305 = term106.
Proof. exact (@lem2524242 term100). Qed.
Lemma lem2524244 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524245 : term306 = term294.
Proof. exact (MK_COMB (@lem2524244) (@lem2524243)). Qed.
Lemma lem2524246 : term303 = term292.
Proof. exact (MK_COMB (@lem2524245) (@lem2524240)). Qed.
Lemma lem2524248 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524249 : term292 = term309.
Proof. exact (@lem2524248 (NUMERAL 0) term100). Qed.
Lemma lem2524250 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524251 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524252 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524251 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524250)). Qed.
Lemma lem2524253 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524252) (@lem2524250)). Qed.
Lemma lem2524254 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524256 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524255) (@lem2524254)). Qed.
Lemma lem2524257 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524256) (@lem2524253)). Qed.
Lemma lem2524259 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524260 : term309 = False.
Proof. exact (TRANS (@lem2524257) (@lem2524259)). Qed.
Lemma lem2524261 : term292 = False.
Proof. exact (TRANS (@lem2524249) (@lem2524260)). Qed.
Lemma lem2524262 : term303 = False.
Proof. exact (TRANS (@lem2524246) (@lem2524261)). Qed.
Lemma lem2524263 : term296 = False.
Proof. exact (TRANS (@lem2524230) (@lem2524262)). Qed.
Lemma lem2524264 : term292 = False.
Proof. exact (TRANS (@lem2524207) (@lem2524263)). Qed.
Lemma lem2524265 : term233 = False.
Proof. exact (TRANS (@lem2524198) (@lem2524264)). Qed.
Lemma lem2524266 (n : int) (h1 : term291 n) : False.
Proof. exact (EQ_MP (@lem2524265) (@lem2524194 n h1)). Qed.
Lemma lem2524267 (n : int) (h1 : term311 n) : term311 n.
Proof. exact (h1). Qed.
Lemma lem2524268 (n : int) (h1 : term311 n) : term233.
Proof. exact (proj2 (@lem2524267 n h1)). Qed.
Lemma lem2524271 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524272 : term233 = term292.
Proof. exact (@lem2524271 term106 term183). Qed.
Lemma lem2524274 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524275 : term183 = term188.
Proof. exact (@lem2524274 term100). Qed.
Lemma lem2524277 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524278 : term106 = term293.
Proof. exact (@lem2524277 (NUMERAL 0)). Qed.
Lemma lem2524279 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524280 : term294 = term295.
Proof. exact (MK_COMB (@lem2524279) (@lem2524278)). Qed.
Lemma lem2524281 : term292 = term296.
Proof. exact (MK_COMB (@lem2524280) (@lem2524275)). Qed.
Lemma lem2524282 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524284 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524285 : term299 = term300.
Proof. exact (@lem2524284 (NUMERAL 0) term100). Qed.
Lemma lem2524286 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524287 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524288 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524287 h1) (fun h1 : term300 = True => @lem2524286)). Qed.
Lemma lem2524289 : term300 = True.
Proof. exact (EQ_MP (@lem2524288) (@lem2524286)). Qed.
Lemma lem2524290 : term299 = True.
Proof. exact (TRANS (@lem2524285) (@lem2524289)). Qed.
Lemma lem2524291 : True = term299.
Proof. exact (SYM (@lem2524290)). Qed.
Lemma lem2524292 : term299.
Proof. exact (EQ_MP (@lem2524291) (@lem0)). Qed.
Lemma lem2524293 : term302.
Proof. exact (@lem2524282 (@lem2524292)). Qed.
Lemma lem2524295 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524296 : term299 = term300.
Proof. exact (@lem2524295 (NUMERAL 0) term100). Qed.
Lemma lem2524297 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524298 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524299 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524298 h1) (fun h1 : term300 = True => @lem2524297)). Qed.
Lemma lem2524300 : term300 = True.
Proof. exact (EQ_MP (@lem2524299) (@lem2524297)). Qed.
Lemma lem2524301 : term299 = True.
Proof. exact (TRANS (@lem2524296) (@lem2524300)). Qed.
Lemma lem2524302 : True = term299.
Proof. exact (SYM (@lem2524301)). Qed.
Lemma lem2524303 : term299.
Proof. exact (EQ_MP (@lem2524302) (@lem0)). Qed.
Lemma lem2524304 : term296 = term303.
Proof. exact (@lem2524293 (@lem2524303)). Qed.
Lemma lem2524306 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524307 : term191 = term202.
Proof. exact (@lem2524306 term100 term100). Qed.
Lemma lem2524308 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524309 : term199 = term100.
Proof. exact (EQ_MP (@lem2524308) (@lem940073)). Qed.
Lemma lem2524310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524311 : term197 = term99.
Proof. exact (MK_COMB (@lem2524310) (@lem2524309)). Qed.
Lemma lem2524312 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524313 : term202 = term183.
Proof. exact (MK_COMB (@lem2524312) (@lem2524311)). Qed.
Lemma lem2524314 : term191 = term183.
Proof. exact (TRANS (@lem2524307) (@lem2524313)). Qed.
Lemma lem2524316 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524317 : term305 = term106.
Proof. exact (@lem2524316 term100). Qed.
Lemma lem2524318 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524319 : term306 = term294.
Proof. exact (MK_COMB (@lem2524318) (@lem2524317)). Qed.
Lemma lem2524320 : term303 = term292.
Proof. exact (MK_COMB (@lem2524319) (@lem2524314)). Qed.
Lemma lem2524322 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524323 : term292 = term309.
Proof. exact (@lem2524322 (NUMERAL 0) term100). Qed.
Lemma lem2524324 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524325 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524326 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524325 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524324)). Qed.
Lemma lem2524327 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524326) (@lem2524324)). Qed.
Lemma lem2524328 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524330 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524329) (@lem2524328)). Qed.
Lemma lem2524331 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524330) (@lem2524327)). Qed.
Lemma lem2524333 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524334 : term309 = False.
Proof. exact (TRANS (@lem2524331) (@lem2524333)). Qed.
Lemma lem2524335 : term292 = False.
Proof. exact (TRANS (@lem2524323) (@lem2524334)). Qed.
Lemma lem2524336 : term303 = False.
Proof. exact (TRANS (@lem2524320) (@lem2524335)). Qed.
Lemma lem2524337 : term296 = False.
Proof. exact (TRANS (@lem2524304) (@lem2524336)). Qed.
Lemma lem2524338 : term292 = False.
Proof. exact (TRANS (@lem2524281) (@lem2524337)). Qed.
Lemma lem2524339 : term233 = False.
Proof. exact (TRANS (@lem2524272) (@lem2524338)). Qed.
Lemma lem2524340 (n : int) (h1 : term311 n) : False.
Proof. exact (EQ_MP (@lem2524339) (@lem2524268 n h1)). Qed.
Lemma lem2524341 (n : int) (h1 : term260 n) : False.
Proof. exact (or_elim (@lem2524192 n h1) (fun h0 : term291 n => @lem2524266 n h0) (fun h0 : term311 n => @lem2524340 n h0)). Qed.
Lemma lem2524342 (n : int) (h1 : term288 n) : term288 n.
Proof. exact (h1). Qed.
Lemma lem2524343 (n : int) (h1 : term282 n) : term282 n.
Proof. exact (h1). Qed.
Lemma lem2524344 (n : int) (h1 : term282 n) : term279 n.
Proof. exact (proj2 (@lem2524343 n h1)). Qed.
Lemma lem2524345 (n : int) (h1 : term282 n) : term211 n.
Proof. exact (proj1 (@lem2524343 n h1)). Qed.
Lemma lem2524346 (n : int) (h1 : term282 n) : term277 n.
Proof. exact (proj2 (@lem2524344 n h1)). Qed.
Lemma lem2524349 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2524350 : term312 = term299.
Proof. exact (@lem2524349 term106 term99). Qed.
Lemma lem2524352 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524353 : term99 = term185.
Proof. exact (@lem2524352 term100). Qed.
Lemma lem2524355 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524356 : term106 = term293.
Proof. exact (@lem2524355 (NUMERAL 0)). Qed.
Lemma lem2524357 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524358 : term313 = term314.
Proof. exact (MK_COMB (@lem2524357) (@lem2524356)). Qed.
Lemma lem2524359 : term299 = term315.
Proof. exact (MK_COMB (@lem2524358) (@lem2524353)). Qed.
Lemma lem2524360 : term316.
Proof. exact (@lem1980255 term106 term99 term99 term99). Qed.
Lemma lem2524362 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524363 : term299 = term300.
Proof. exact (@lem2524362 (NUMERAL 0) term100). Qed.
Lemma lem2524364 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524365 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524366 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524365 h1) (fun h1 : term300 = True => @lem2524364)). Qed.
Lemma lem2524367 : term300 = True.
Proof. exact (EQ_MP (@lem2524366) (@lem2524364)). Qed.
Lemma lem2524368 : term299 = True.
Proof. exact (TRANS (@lem2524363) (@lem2524367)). Qed.
Lemma lem2524369 : True = term299.
Proof. exact (SYM (@lem2524368)). Qed.
Lemma lem2524370 : term299.
Proof. exact (EQ_MP (@lem2524369) (@lem0)). Qed.
Lemma lem2524371 : term317.
Proof. exact (@lem2524360 (@lem2524370)). Qed.
Lemma lem2524373 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524374 : term299 = term300.
Proof. exact (@lem2524373 (NUMERAL 0) term100). Qed.
Lemma lem2524375 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524376 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524377 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524376 h1) (fun h1 : term300 = True => @lem2524375)). Qed.
Lemma lem2524378 : term300 = True.
Proof. exact (EQ_MP (@lem2524377) (@lem2524375)). Qed.
Lemma lem2524379 : term299 = True.
Proof. exact (TRANS (@lem2524374) (@lem2524378)). Qed.
Lemma lem2524380 : True = term299.
Proof. exact (SYM (@lem2524379)). Qed.
Lemma lem2524381 : term299.
Proof. exact (EQ_MP (@lem2524380) (@lem0)). Qed.
Lemma lem2524382 : term315 = term318.
Proof. exact (@lem2524371 (@lem2524381)). Qed.
Lemma lem2524384 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524385 : term196 = term197.
Proof. exact (@lem2524384 term100 term100). Qed.
Lemma lem2524386 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524387 : term199 = term100.
Proof. exact (EQ_MP (@lem2524386) (@lem940073)). Qed.
Lemma lem2524388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524389 : term197 = term99.
Proof. exact (MK_COMB (@lem2524388) (@lem2524387)). Qed.
Lemma lem2524390 : term196 = term99.
Proof. exact (TRANS (@lem2524385) (@lem2524389)). Qed.
Lemma lem2524392 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524393 : term305 = term106.
Proof. exact (@lem2524392 term100). Qed.
Lemma lem2524394 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524395 : term319 = term313.
Proof. exact (MK_COMB (@lem2524394) (@lem2524393)). Qed.
Lemma lem2524396 : term318 = term299.
Proof. exact (MK_COMB (@lem2524395) (@lem2524390)). Qed.
Lemma lem2524398 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524399 : term299 = term300.
Proof. exact (@lem2524398 (NUMERAL 0) term100). Qed.
Lemma lem2524400 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524401 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524402 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524401 h1) (fun h1 : term300 = True => @lem2524400)). Qed.
Lemma lem2524403 : term300 = True.
Proof. exact (EQ_MP (@lem2524402) (@lem2524400)). Qed.
Lemma lem2524404 : term299 = True.
Proof. exact (TRANS (@lem2524399) (@lem2524403)). Qed.
Lemma lem2524405 : term318 = True.
Proof. exact (TRANS (@lem2524396) (@lem2524404)). Qed.
Lemma lem2524406 : term315 = True.
Proof. exact (TRANS (@lem2524382) (@lem2524405)). Qed.
Lemma lem2524407 : term299 = True.
Proof. exact (TRANS (@lem2524359) (@lem2524406)). Qed.
Lemma lem2524408 : term312 = True.
Proof. exact (TRANS (@lem2524350) (@lem2524407)). Qed.
Lemma lem2524409 : True = term312.
Proof. exact (SYM (@lem2524408)). Qed.
Lemma lem2524410 : term312.
Proof. exact (EQ_MP (@lem2524409) (@lem0)). Qed.
Lemma lem2524411 (n : int) (h1 : term282 n) : term320 n.
Proof. exact (conj (@lem2524410) (@lem2524346 n h1)). Qed.
Lemma lem2524413 (x : real) (y : real) : term321 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2524414 (n : int) : term322 n.
Proof. exact (@lem2524413 term99 (real_of_int n)). Qed.
Lemma lem2524415 (n : int) (h1 : term282 n) : term276 n.
Proof. exact (@lem2524414 n (@lem2524411 n h1)). Qed.
Lemma lem2524416 (n : int) : (term273 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2524417 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524418 (n : int) : (term274 n) = (term275 n).
Proof. exact (MK_COMB (@lem2524417) (@lem2524416 n)). Qed.
Lemma lem2524419 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524420 (n : int) : (term276 n) = (term277 n).
Proof. exact (MK_COMB (@lem2524418 n) (@lem2524419)). Qed.
Lemma lem2524421 (n : int) (h1 : term282 n) : term277 n.
Proof. exact (EQ_MP (@lem2524420 n) (@lem2524415 n h1)). Qed.
Lemma lem2524423 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2524424 : term312 = term299.
Proof. exact (@lem2524423 term106 term99). Qed.
Lemma lem2524426 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524427 : term99 = term185.
Proof. exact (@lem2524426 term100). Qed.
Lemma lem2524429 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524430 : term106 = term293.
Proof. exact (@lem2524429 (NUMERAL 0)). Qed.
Lemma lem2524431 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524432 : term313 = term314.
Proof. exact (MK_COMB (@lem2524431) (@lem2524430)). Qed.
Lemma lem2524433 : term299 = term315.
Proof. exact (MK_COMB (@lem2524432) (@lem2524427)). Qed.
Lemma lem2524434 : term316.
Proof. exact (@lem1980255 term106 term99 term99 term99). Qed.
Lemma lem2524436 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524437 : term299 = term300.
Proof. exact (@lem2524436 (NUMERAL 0) term100). Qed.
Lemma lem2524438 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524439 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524440 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524439 h1) (fun h1 : term300 = True => @lem2524438)). Qed.
Lemma lem2524441 : term300 = True.
Proof. exact (EQ_MP (@lem2524440) (@lem2524438)). Qed.
Lemma lem2524442 : term299 = True.
Proof. exact (TRANS (@lem2524437) (@lem2524441)). Qed.
Lemma lem2524443 : True = term299.
Proof. exact (SYM (@lem2524442)). Qed.
Lemma lem2524444 : term299.
Proof. exact (EQ_MP (@lem2524443) (@lem0)). Qed.
Lemma lem2524445 : term317.
Proof. exact (@lem2524434 (@lem2524444)). Qed.
Lemma lem2524447 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524448 : term299 = term300.
Proof. exact (@lem2524447 (NUMERAL 0) term100). Qed.
Lemma lem2524449 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524450 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524451 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524450 h1) (fun h1 : term300 = True => @lem2524449)). Qed.
Lemma lem2524452 : term300 = True.
Proof. exact (EQ_MP (@lem2524451) (@lem2524449)). Qed.
Lemma lem2524453 : term299 = True.
Proof. exact (TRANS (@lem2524448) (@lem2524452)). Qed.
Lemma lem2524454 : True = term299.
Proof. exact (SYM (@lem2524453)). Qed.
Lemma lem2524455 : term299.
Proof. exact (EQ_MP (@lem2524454) (@lem0)). Qed.
Lemma lem2524456 : term315 = term318.
Proof. exact (@lem2524445 (@lem2524455)). Qed.
Lemma lem2524458 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524459 : term196 = term197.
Proof. exact (@lem2524458 term100 term100). Qed.
Lemma lem2524460 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524461 : term199 = term100.
Proof. exact (EQ_MP (@lem2524460) (@lem940073)). Qed.
Lemma lem2524462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524463 : term197 = term99.
Proof. exact (MK_COMB (@lem2524462) (@lem2524461)). Qed.
Lemma lem2524464 : term196 = term99.
Proof. exact (TRANS (@lem2524459) (@lem2524463)). Qed.
Lemma lem2524466 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524467 : term305 = term106.
Proof. exact (@lem2524466 term100). Qed.
Lemma lem2524468 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524469 : term319 = term313.
Proof. exact (MK_COMB (@lem2524468) (@lem2524467)). Qed.
Lemma lem2524470 : term318 = term299.
Proof. exact (MK_COMB (@lem2524469) (@lem2524464)). Qed.
Lemma lem2524472 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524473 : term299 = term300.
Proof. exact (@lem2524472 (NUMERAL 0) term100). Qed.
Lemma lem2524474 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524475 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524476 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524475 h1) (fun h1 : term300 = True => @lem2524474)). Qed.
Lemma lem2524477 : term300 = True.
Proof. exact (EQ_MP (@lem2524476) (@lem2524474)). Qed.
Lemma lem2524478 : term299 = True.
Proof. exact (TRANS (@lem2524473) (@lem2524477)). Qed.
Lemma lem2524479 : term318 = True.
Proof. exact (TRANS (@lem2524470) (@lem2524478)). Qed.
Lemma lem2524480 : term315 = True.
Proof. exact (TRANS (@lem2524456) (@lem2524479)). Qed.
Lemma lem2524481 : term299 = True.
Proof. exact (TRANS (@lem2524433) (@lem2524480)). Qed.
Lemma lem2524482 : term312 = True.
Proof. exact (TRANS (@lem2524424) (@lem2524481)). Qed.
Lemma lem2524483 : True = term312.
Proof. exact (SYM (@lem2524482)). Qed.
Lemma lem2524484 : term312.
Proof. exact (EQ_MP (@lem2524483) (@lem0)). Qed.
Lemma lem2524485 (n : int) (h1 : term282 n) : term323 n.
Proof. exact (conj (@lem2524484) (@lem2524345 n h1)). Qed.
Lemma lem2524487 (x : real) (y : real) : term321 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2524488 (n : int) : term324 n.
Proof. exact (@lem2524487 term99 (term207 n)). Qed.
Lemma lem2524489 (n : int) (h1 : term282 n) : term325 n.
Proof. exact (@lem2524488 n (@lem2524485 n h1)). Qed.
Lemma lem2524490 (n : int) : (term326 n) = (term207 n).
Proof. exact (@lem1982733 (term207 n)). Qed.
Lemma lem2524491 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524492 (n : int) : (term327 n) = (term210 n).
Proof. exact (MK_COMB (@lem2524491) (@lem2524490 n)). Qed.
Lemma lem2524493 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524494 (n : int) : (term325 n) = (term211 n).
Proof. exact (MK_COMB (@lem2524492 n) (@lem2524493)). Qed.
Lemma lem2524495 (n : int) (h1 : term282 n) : term211 n.
Proof. exact (EQ_MP (@lem2524494 n) (@lem2524489 n h1)). Qed.
Lemma lem2524496 (n : int) (h1 : term282 n) : term328 n.
Proof. exact (conj (@lem2524495 n h1) (@lem2524421 n h1)). Qed.
Lemma lem2524498 (x : real) (y : real) : term329 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2524499 (n : int) : term330 n.
Proof. exact (@lem2524498 (term207 n) (real_of_int n)). Qed.
Lemma lem2524500 (n : int) (h1 : term282 n) : term331 n.
Proof. exact (@lem2524499 n (@lem2524496 n h1)). Qed.
Lemma lem2524501 (n : int) : (term332 n) = (term333 n).
Proof. exact (@lem1982759 (term334 n) (real_of_int n) term183). Qed.
Lemma lem2524502 (n : int) : (term335 n) = (term336 n).
Proof. exact (@lem1982713 term183 (real_of_int n)). Qed.
Lemma lem2524504 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524505 : term99 = term185.
Proof. exact (@lem2524504 term100). Qed.
Lemma lem2524507 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524508 : term183 = term188.
Proof. exact (@lem2524507 term100). Qed.
Lemma lem2524509 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524510 : term337 = term338.
Proof. exact (MK_COMB (@lem2524509) (@lem2524508)). Qed.
Lemma lem2524511 : term339 = term340.
Proof. exact (MK_COMB (@lem2524510) (@lem2524505)). Qed.
Lemma lem2524512 : term341.
Proof. exact (@lem1981473 term183 term99 term99 term99 term106 term99). Qed.
Lemma lem2524514 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524515 : term299 = term300.
Proof. exact (@lem2524514 (NUMERAL 0) term100). Qed.
Lemma lem2524516 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524517 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524518 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524517 h1) (fun h1 : term300 = True => @lem2524516)). Qed.
Lemma lem2524519 : term300 = True.
Proof. exact (EQ_MP (@lem2524518) (@lem2524516)). Qed.
Lemma lem2524520 : term299 = True.
Proof. exact (TRANS (@lem2524515) (@lem2524519)). Qed.
Lemma lem2524521 : True = term299.
Proof. exact (SYM (@lem2524520)). Qed.
Lemma lem2524522 : term299.
Proof. exact (EQ_MP (@lem2524521) (@lem0)). Qed.
Lemma lem2524523 : term342.
Proof. exact (@lem2524512 (@lem2524522)). Qed.
Lemma lem2524525 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524526 : term299 = term300.
Proof. exact (@lem2524525 (NUMERAL 0) term100). Qed.
Lemma lem2524527 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524528 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524529 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524528 h1) (fun h1 : term300 = True => @lem2524527)). Qed.
Lemma lem2524530 : term300 = True.
Proof. exact (EQ_MP (@lem2524529) (@lem2524527)). Qed.
Lemma lem2524531 : term299 = True.
Proof. exact (TRANS (@lem2524526) (@lem2524530)). Qed.
Lemma lem2524532 : True = term299.
Proof. exact (SYM (@lem2524531)). Qed.
Lemma lem2524533 : term299.
Proof. exact (EQ_MP (@lem2524532) (@lem0)). Qed.
Lemma lem2524534 : term343.
Proof. exact (@lem2524523 (@lem2524533)). Qed.
Lemma lem2524536 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524537 : term299 = term300.
Proof. exact (@lem2524536 (NUMERAL 0) term100). Qed.
Lemma lem2524538 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524539 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524540 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524539 h1) (fun h1 : term300 = True => @lem2524538)). Qed.
Lemma lem2524541 : term300 = True.
Proof. exact (EQ_MP (@lem2524540) (@lem2524538)). Qed.
Lemma lem2524542 : term299 = True.
Proof. exact (TRANS (@lem2524537) (@lem2524541)). Qed.
Lemma lem2524543 : True = term299.
Proof. exact (SYM (@lem2524542)). Qed.
Lemma lem2524544 : term299.
Proof. exact (EQ_MP (@lem2524543) (@lem0)). Qed.
Lemma lem2524545 : term344.
Proof. exact (@lem2524534 (@lem2524544)). Qed.
Lemma lem2524547 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524548 : term196 = term197.
Proof. exact (@lem2524547 term100 term100). Qed.
Lemma lem2524549 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524550 : term199 = term100.
Proof. exact (EQ_MP (@lem2524549) (@lem940073)). Qed.
Lemma lem2524551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524552 : term197 = term99.
Proof. exact (MK_COMB (@lem2524551) (@lem2524550)). Qed.
Lemma lem2524553 : term196 = term99.
Proof. exact (TRANS (@lem2524548) (@lem2524552)). Qed.
Lemma lem2524555 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524556 : term191 = term202.
Proof. exact (@lem2524555 term100 term100). Qed.
Lemma lem2524557 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524558 : term199 = term100.
Proof. exact (EQ_MP (@lem2524557) (@lem940073)). Qed.
Lemma lem2524559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524560 : term197 = term99.
Proof. exact (MK_COMB (@lem2524559) (@lem2524558)). Qed.
Lemma lem2524561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524562 : term202 = term183.
Proof. exact (MK_COMB (@lem2524561) (@lem2524560)). Qed.
Lemma lem2524563 : term191 = term183.
Proof. exact (TRANS (@lem2524556) (@lem2524562)). Qed.
Lemma lem2524564 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524565 : term345 = term337.
Proof. exact (MK_COMB (@lem2524564) (@lem2524563)). Qed.
Lemma lem2524566 : term346 = term339.
Proof. exact (MK_COMB (@lem2524565) (@lem2524553)). Qed.
Lemma lem2524568 (m : nat) : (term347 m) = term106.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2524569 : term339 = term106.
Proof. exact (@lem2524568 term100). Qed.
Lemma lem2524570 : term346 = term106.
Proof. exact (TRANS (@lem2524566) (@lem2524569)). Qed.
Lemma lem2524571 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2524572 : term348 = term134.
Proof. exact (MK_COMB (@lem2524571) (@lem2524570)). Qed.
Lemma lem2524573 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2524574 : term349 = term305.
Proof. exact (MK_COMB (@lem2524572) (@lem2524573)). Qed.
Lemma lem2524576 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524577 : term305 = term106.
Proof. exact (@lem2524576 term100). Qed.
Lemma lem2524578 : term349 = term106.
Proof. exact (TRANS (@lem2524574) (@lem2524577)). Qed.
Lemma lem2524580 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524581 : term196 = term197.
Proof. exact (@lem2524580 term100 term100). Qed.
Lemma lem2524582 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524583 : term199 = term100.
Proof. exact (EQ_MP (@lem2524582) (@lem940073)). Qed.
Lemma lem2524584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524585 : term197 = term99.
Proof. exact (MK_COMB (@lem2524584) (@lem2524583)). Qed.
Lemma lem2524586 : term196 = term99.
Proof. exact (TRANS (@lem2524581) (@lem2524585)). Qed.
Lemma lem2524587 : term134 = term134.
Proof. exact (eq_refl term134). Qed.
Lemma lem2524588 : term350 = term305.
Proof. exact (MK_COMB (@lem2524587) (@lem2524586)). Qed.
Lemma lem2524590 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524591 : term305 = term106.
Proof. exact (@lem2524590 term100). Qed.
Lemma lem2524592 : term350 = term106.
Proof. exact (TRANS (@lem2524588) (@lem2524591)). Qed.
Lemma lem2524593 : term106 = term350.
Proof. exact (SYM (@lem2524592)). Qed.
Lemma lem2524594 : term349 = term350.
Proof. exact (TRANS (@lem2524578) (@lem2524593)). Qed.
Lemma lem2524595 : term340 = term293.
Proof. exact (@lem2524545 (@lem2524594)). Qed.
Lemma lem2524596 : term339 = term293.
Proof. exact (TRANS (@lem2524511) (@lem2524595)). Qed.
Lemma lem2524598 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2524599 : term293 = term106.
Proof. exact (@lem2524598 term106). Qed.
Lemma lem2524600 : term339 = term106.
Proof. exact (TRANS (@lem2524596) (@lem2524599)). Qed.
Lemma lem2524601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2524602 : term351 = term134.
Proof. exact (MK_COMB (@lem2524601) (@lem2524600)). Qed.
Lemma lem2524603 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2524604 (n : int) : (term336 n) = (term135 n).
Proof. exact (MK_COMB (@lem2524602) (@lem2524603 n)). Qed.
Lemma lem2524605 (n : int) : (term335 n) = (term135 n).
Proof. exact (TRANS (@lem2524502 n) (@lem2524604 n)). Qed.
Lemma lem2524606 (n : int) : (term135 n) = term106.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2524607 (n : int) : (term335 n) = term106.
Proof. exact (TRANS (@lem2524605 n) (@lem2524606 n)). Qed.
Lemma lem2524608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524609 (n : int) : (term352 n) = term116.
Proof. exact (MK_COMB (@lem2524608) (@lem2524607 n)). Qed.
Lemma lem2524610 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2524611 (n : int) : (term333 n) = term230.
Proof. exact (MK_COMB (@lem2524609 n) (@lem2524610)). Qed.
Lemma lem2524612 (n : int) : (term332 n) = term230.
Proof. exact (TRANS (@lem2524501 n) (@lem2524611 n)). Qed.
Lemma lem2524613 : term230 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2524614 (n : int) : (term332 n) = term183.
Proof. exact (TRANS (@lem2524612 n) (@lem2524613)). Qed.
Lemma lem2524615 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524616 (n : int) : (term353 n) = term232.
Proof. exact (MK_COMB (@lem2524615) (@lem2524614 n)). Qed.
Lemma lem2524617 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524618 (n : int) : (term331 n) = term233.
Proof. exact (MK_COMB (@lem2524616 n) (@lem2524617)). Qed.
Lemma lem2524619 (n : int) (h1 : term282 n) : term233.
Proof. exact (EQ_MP (@lem2524618 n) (@lem2524500 n h1)). Qed.
Lemma lem2524621 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524622 : term233 = term292.
Proof. exact (@lem2524621 term106 term183). Qed.
Lemma lem2524624 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524625 : term183 = term188.
Proof. exact (@lem2524624 term100). Qed.
Lemma lem2524627 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524628 : term106 = term293.
Proof. exact (@lem2524627 (NUMERAL 0)). Qed.
Lemma lem2524629 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524630 : term294 = term295.
Proof. exact (MK_COMB (@lem2524629) (@lem2524628)). Qed.
Lemma lem2524631 : term292 = term296.
Proof. exact (MK_COMB (@lem2524630) (@lem2524625)). Qed.
Lemma lem2524632 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524634 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524635 : term299 = term300.
Proof. exact (@lem2524634 (NUMERAL 0) term100). Qed.
Lemma lem2524636 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524637 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524638 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524637 h1) (fun h1 : term300 = True => @lem2524636)). Qed.
Lemma lem2524639 : term300 = True.
Proof. exact (EQ_MP (@lem2524638) (@lem2524636)). Qed.
Lemma lem2524640 : term299 = True.
Proof. exact (TRANS (@lem2524635) (@lem2524639)). Qed.
Lemma lem2524641 : True = term299.
Proof. exact (SYM (@lem2524640)). Qed.
Lemma lem2524642 : term299.
Proof. exact (EQ_MP (@lem2524641) (@lem0)). Qed.
Lemma lem2524643 : term302.
Proof. exact (@lem2524632 (@lem2524642)). Qed.
Lemma lem2524645 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524646 : term299 = term300.
Proof. exact (@lem2524645 (NUMERAL 0) term100). Qed.
Lemma lem2524647 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524648 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524649 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524648 h1) (fun h1 : term300 = True => @lem2524647)). Qed.
Lemma lem2524650 : term300 = True.
Proof. exact (EQ_MP (@lem2524649) (@lem2524647)). Qed.
Lemma lem2524651 : term299 = True.
Proof. exact (TRANS (@lem2524646) (@lem2524650)). Qed.
Lemma lem2524652 : True = term299.
Proof. exact (SYM (@lem2524651)). Qed.
Lemma lem2524653 : term299.
Proof. exact (EQ_MP (@lem2524652) (@lem0)). Qed.
Lemma lem2524654 : term296 = term303.
Proof. exact (@lem2524643 (@lem2524653)). Qed.
Lemma lem2524656 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524657 : term191 = term202.
Proof. exact (@lem2524656 term100 term100). Qed.
Lemma lem2524658 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524659 : term199 = term100.
Proof. exact (EQ_MP (@lem2524658) (@lem940073)). Qed.
Lemma lem2524660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524661 : term197 = term99.
Proof. exact (MK_COMB (@lem2524660) (@lem2524659)). Qed.
Lemma lem2524662 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524663 : term202 = term183.
Proof. exact (MK_COMB (@lem2524662) (@lem2524661)). Qed.
Lemma lem2524664 : term191 = term183.
Proof. exact (TRANS (@lem2524657) (@lem2524663)). Qed.
Lemma lem2524666 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524667 : term305 = term106.
Proof. exact (@lem2524666 term100). Qed.
Lemma lem2524668 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524669 : term306 = term294.
Proof. exact (MK_COMB (@lem2524668) (@lem2524667)). Qed.
Lemma lem2524670 : term303 = term292.
Proof. exact (MK_COMB (@lem2524669) (@lem2524664)). Qed.
Lemma lem2524672 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2524673 : term292 = term309.
Proof. exact (@lem2524672 (NUMERAL 0) term100). Qed.
Lemma lem2524674 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524675 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2524676 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524675 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2524674)). Qed.
Lemma lem2524677 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2524676) (@lem2524674)). Qed.
Lemma lem2524678 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2524679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2524680 : term310 = (and True).
Proof. exact (MK_COMB (@lem2524679) (@lem2524678)). Qed.
Lemma lem2524681 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2524680) (@lem2524677)). Qed.
Lemma lem2524683 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2524684 : term309 = False.
Proof. exact (TRANS (@lem2524681) (@lem2524683)). Qed.
Lemma lem2524685 : term292 = False.
Proof. exact (TRANS (@lem2524673) (@lem2524684)). Qed.
Lemma lem2524686 : term303 = False.
Proof. exact (TRANS (@lem2524670) (@lem2524685)). Qed.
Lemma lem2524687 : term296 = False.
Proof. exact (TRANS (@lem2524654) (@lem2524686)). Qed.
Lemma lem2524688 : term292 = False.
Proof. exact (TRANS (@lem2524631) (@lem2524687)). Qed.
Lemma lem2524689 : term233 = False.
Proof. exact (TRANS (@lem2524622) (@lem2524688)). Qed.
Lemma lem2524690 (n : int) (h1 : term282 n) : False.
Proof. exact (EQ_MP (@lem2524689) (@lem2524619 n h1)). Qed.
Lemma lem2524691 (n : int) (h1 : term285 n) : term285 n.
Proof. exact (h1). Qed.
Lemma lem2524692 (n : int) (h1 : term285 n) : term279 n.
Proof. exact (proj2 (@lem2524691 n h1)). Qed.
Lemma lem2524693 (n : int) (h1 : term285 n) : term220 n.
Proof. exact (proj1 (@lem2524691 n h1)). Qed.
Lemma lem2524695 (n : int) (h1 : term285 n) : term354 n.
Proof. exact (proj1 (@lem2524692 n h1)). Qed.
Lemma lem2524697 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2524698 : term312 = term299.
Proof. exact (@lem2524697 term106 term99). Qed.
Lemma lem2524700 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524701 : term99 = term185.
Proof. exact (@lem2524700 term100). Qed.
Lemma lem2524703 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524704 : term106 = term293.
Proof. exact (@lem2524703 (NUMERAL 0)). Qed.
Lemma lem2524705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524706 : term313 = term314.
Proof. exact (MK_COMB (@lem2524705) (@lem2524704)). Qed.
Lemma lem2524707 : term299 = term315.
Proof. exact (MK_COMB (@lem2524706) (@lem2524701)). Qed.
Lemma lem2524708 : term316.
Proof. exact (@lem1980255 term106 term99 term99 term99). Qed.
Lemma lem2524710 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524711 : term299 = term300.
Proof. exact (@lem2524710 (NUMERAL 0) term100). Qed.
Lemma lem2524712 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524713 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524714 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524713 h1) (fun h1 : term300 = True => @lem2524712)). Qed.
Lemma lem2524715 : term300 = True.
Proof. exact (EQ_MP (@lem2524714) (@lem2524712)). Qed.
Lemma lem2524716 : term299 = True.
Proof. exact (TRANS (@lem2524711) (@lem2524715)). Qed.
Lemma lem2524717 : True = term299.
Proof. exact (SYM (@lem2524716)). Qed.
Lemma lem2524718 : term299.
Proof. exact (EQ_MP (@lem2524717) (@lem0)). Qed.
Lemma lem2524719 : term317.
Proof. exact (@lem2524708 (@lem2524718)). Qed.
Lemma lem2524721 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524722 : term299 = term300.
Proof. exact (@lem2524721 (NUMERAL 0) term100). Qed.
Lemma lem2524723 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524724 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524725 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524724 h1) (fun h1 : term300 = True => @lem2524723)). Qed.
Lemma lem2524726 : term300 = True.
Proof. exact (EQ_MP (@lem2524725) (@lem2524723)). Qed.
Lemma lem2524727 : term299 = True.
Proof. exact (TRANS (@lem2524722) (@lem2524726)). Qed.
Lemma lem2524728 : True = term299.
Proof. exact (SYM (@lem2524727)). Qed.
Lemma lem2524729 : term299.
Proof. exact (EQ_MP (@lem2524728) (@lem0)). Qed.
Lemma lem2524730 : term315 = term318.
Proof. exact (@lem2524719 (@lem2524729)). Qed.
Lemma lem2524732 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524733 : term196 = term197.
Proof. exact (@lem2524732 term100 term100). Qed.
Lemma lem2524734 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524735 : term199 = term100.
Proof. exact (EQ_MP (@lem2524734) (@lem940073)). Qed.
Lemma lem2524736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524737 : term197 = term99.
Proof. exact (MK_COMB (@lem2524736) (@lem2524735)). Qed.
Lemma lem2524738 : term196 = term99.
Proof. exact (TRANS (@lem2524733) (@lem2524737)). Qed.
Lemma lem2524740 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524741 : term305 = term106.
Proof. exact (@lem2524740 term100). Qed.
Lemma lem2524742 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524743 : term319 = term313.
Proof. exact (MK_COMB (@lem2524742) (@lem2524741)). Qed.
Lemma lem2524744 : term318 = term299.
Proof. exact (MK_COMB (@lem2524743) (@lem2524738)). Qed.
Lemma lem2524746 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524747 : term299 = term300.
Proof. exact (@lem2524746 (NUMERAL 0) term100). Qed.
Lemma lem2524748 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524749 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524750 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524749 h1) (fun h1 : term300 = True => @lem2524748)). Qed.
Lemma lem2524751 : term300 = True.
Proof. exact (EQ_MP (@lem2524750) (@lem2524748)). Qed.
Lemma lem2524752 : term299 = True.
Proof. exact (TRANS (@lem2524747) (@lem2524751)). Qed.
Lemma lem2524753 : term318 = True.
Proof. exact (TRANS (@lem2524744) (@lem2524752)). Qed.
Lemma lem2524754 : term315 = True.
Proof. exact (TRANS (@lem2524730) (@lem2524753)). Qed.
Lemma lem2524755 : term299 = True.
Proof. exact (TRANS (@lem2524707) (@lem2524754)). Qed.
Lemma lem2524756 : term312 = True.
Proof. exact (TRANS (@lem2524698) (@lem2524755)). Qed.
Lemma lem2524757 : True = term312.
Proof. exact (SYM (@lem2524756)). Qed.
Lemma lem2524758 : term312.
Proof. exact (EQ_MP (@lem2524757) (@lem0)). Qed.
Lemma lem2524759 (n : int) (h1 : term285 n) : term355 n.
Proof. exact (conj (@lem2524758) (@lem2524693 n h1)). Qed.
Lemma lem2524761 (x : real) (y : real) : term321 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2524762 (n : int) : term356 n.
Proof. exact (@lem2524761 term99 (term217 n)). Qed.
Lemma lem2524763 (n : int) (h1 : term285 n) : term357 n.
Proof. exact (@lem2524762 n (@lem2524759 n h1)). Qed.
Lemma lem2524764 (n : int) : (term358 n) = (term217 n).
Proof. exact (@lem1982733 (term217 n)). Qed.
Lemma lem2524765 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524766 (n : int) : (term359 n) = (term219 n).
Proof. exact (MK_COMB (@lem2524765) (@lem2524764 n)). Qed.
Lemma lem2524767 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524768 (n : int) : (term357 n) = (term220 n).
Proof. exact (MK_COMB (@lem2524766 n) (@lem2524767)). Qed.
Lemma lem2524769 (n : int) (h1 : term285 n) : term220 n.
Proof. exact (EQ_MP (@lem2524768 n) (@lem2524763 n h1)). Qed.
Lemma lem2524771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2524772 : term312 = term299.
Proof. exact (@lem2524771 term106 term99). Qed.
Lemma lem2524774 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524775 : term99 = term185.
Proof. exact (@lem2524774 term100). Qed.
Lemma lem2524777 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524778 : term106 = term293.
Proof. exact (@lem2524777 (NUMERAL 0)). Qed.
Lemma lem2524779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524780 : term313 = term314.
Proof. exact (MK_COMB (@lem2524779) (@lem2524778)). Qed.
Lemma lem2524781 : term299 = term315.
Proof. exact (MK_COMB (@lem2524780) (@lem2524775)). Qed.
Lemma lem2524782 : term316.
Proof. exact (@lem1980255 term106 term99 term99 term99). Qed.
Lemma lem2524784 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524785 : term299 = term300.
Proof. exact (@lem2524784 (NUMERAL 0) term100). Qed.
Lemma lem2524786 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524787 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524788 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524787 h1) (fun h1 : term300 = True => @lem2524786)). Qed.
Lemma lem2524789 : term300 = True.
Proof. exact (EQ_MP (@lem2524788) (@lem2524786)). Qed.
Lemma lem2524790 : term299 = True.
Proof. exact (TRANS (@lem2524785) (@lem2524789)). Qed.
Lemma lem2524791 : True = term299.
Proof. exact (SYM (@lem2524790)). Qed.
Lemma lem2524792 : term299.
Proof. exact (EQ_MP (@lem2524791) (@lem0)). Qed.
Lemma lem2524793 : term317.
Proof. exact (@lem2524782 (@lem2524792)). Qed.
Lemma lem2524795 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524796 : term299 = term300.
Proof. exact (@lem2524795 (NUMERAL 0) term100). Qed.
Lemma lem2524797 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524798 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524799 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524798 h1) (fun h1 : term300 = True => @lem2524797)). Qed.
Lemma lem2524800 : term300 = True.
Proof. exact (EQ_MP (@lem2524799) (@lem2524797)). Qed.
Lemma lem2524801 : term299 = True.
Proof. exact (TRANS (@lem2524796) (@lem2524800)). Qed.
Lemma lem2524802 : True = term299.
Proof. exact (SYM (@lem2524801)). Qed.
Lemma lem2524803 : term299.
Proof. exact (EQ_MP (@lem2524802) (@lem0)). Qed.
Lemma lem2524804 : term315 = term318.
Proof. exact (@lem2524793 (@lem2524803)). Qed.
Lemma lem2524806 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524807 : term196 = term197.
Proof. exact (@lem2524806 term100 term100). Qed.
Lemma lem2524808 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524809 : term199 = term100.
Proof. exact (EQ_MP (@lem2524808) (@lem940073)). Qed.
Lemma lem2524810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524811 : term197 = term99.
Proof. exact (MK_COMB (@lem2524810) (@lem2524809)). Qed.
Lemma lem2524812 : term196 = term99.
Proof. exact (TRANS (@lem2524807) (@lem2524811)). Qed.
Lemma lem2524814 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524815 : term305 = term106.
Proof. exact (@lem2524814 term100). Qed.
Lemma lem2524816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2524817 : term319 = term313.
Proof. exact (MK_COMB (@lem2524816) (@lem2524815)). Qed.
Lemma lem2524818 : term318 = term299.
Proof. exact (MK_COMB (@lem2524817) (@lem2524812)). Qed.
Lemma lem2524820 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524821 : term299 = term300.
Proof. exact (@lem2524820 (NUMERAL 0) term100). Qed.
Lemma lem2524822 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524823 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524824 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524823 h1) (fun h1 : term300 = True => @lem2524822)). Qed.
Lemma lem2524825 : term300 = True.
Proof. exact (EQ_MP (@lem2524824) (@lem2524822)). Qed.
Lemma lem2524826 : term299 = True.
Proof. exact (TRANS (@lem2524821) (@lem2524825)). Qed.
Lemma lem2524827 : term318 = True.
Proof. exact (TRANS (@lem2524818) (@lem2524826)). Qed.
Lemma lem2524828 : term315 = True.
Proof. exact (TRANS (@lem2524804) (@lem2524827)). Qed.
Lemma lem2524829 : term299 = True.
Proof. exact (TRANS (@lem2524781) (@lem2524828)). Qed.
Lemma lem2524830 : term312 = True.
Proof. exact (TRANS (@lem2524772) (@lem2524829)). Qed.
Lemma lem2524831 : True = term312.
Proof. exact (SYM (@lem2524830)). Qed.
Lemma lem2524832 : term312.
Proof. exact (EQ_MP (@lem2524831) (@lem0)). Qed.
Lemma lem2524833 (n : int) (h1 : term285 n) : term360 n.
Proof. exact (conj (@lem2524832) (@lem2524695 n h1)). Qed.
Lemma lem2524835 (x : real) (y : real) : term321 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2524836 (n : int) : term361 n.
Proof. exact (@lem2524835 term99 (term334 n)). Qed.
Lemma lem2524837 (n : int) (h1 : term285 n) : term362 n.
Proof. exact (@lem2524836 n (@lem2524833 n h1)). Qed.
Lemma lem2524838 (n : int) : (term363 n) = (term334 n).
Proof. exact (@lem1982733 (term334 n)). Qed.
Lemma lem2524839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524840 (n : int) : (term364 n) = (term365 n).
Proof. exact (MK_COMB (@lem2524839) (@lem2524838 n)). Qed.
Lemma lem2524841 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524842 (n : int) : (term362 n) = (term354 n).
Proof. exact (MK_COMB (@lem2524840 n) (@lem2524841)). Qed.
Lemma lem2524843 (n : int) (h1 : term285 n) : term354 n.
Proof. exact (EQ_MP (@lem2524842 n) (@lem2524837 n h1)). Qed.
Lemma lem2524844 (n : int) (h1 : term285 n) : term366 n.
Proof. exact (conj (@lem2524843 n h1) (@lem2524769 n h1)). Qed.
Lemma lem2524846 (x : real) (y : real) : term329 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2524847 (n : int) : term367 n.
Proof. exact (@lem2524846 (term334 n) (term217 n)). Qed.
Lemma lem2524848 (n : int) (h1 : term285 n) : term368 n.
Proof. exact (@lem2524847 n (@lem2524844 n h1)). Qed.
Lemma lem2524849 (n : int) : (term369 n) = (term333 n).
Proof. exact (@lem1982763 (term334 n) (real_of_int n) term183). Qed.
Lemma lem2524850 (n : int) : (term335 n) = (term336 n).
Proof. exact (@lem1982713 term183 (real_of_int n)). Qed.
Lemma lem2524852 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524853 : term99 = term185.
Proof. exact (@lem2524852 term100). Qed.
Lemma lem2524855 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524856 : term183 = term188.
Proof. exact (@lem2524855 term100). Qed.
Lemma lem2524857 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524858 : term337 = term338.
Proof. exact (MK_COMB (@lem2524857) (@lem2524856)). Qed.
Lemma lem2524859 : term339 = term340.
Proof. exact (MK_COMB (@lem2524858) (@lem2524853)). Qed.
Lemma lem2524860 : term341.
Proof. exact (@lem1981473 term183 term99 term99 term99 term106 term99). Qed.
Lemma lem2524862 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524863 : term299 = term300.
Proof. exact (@lem2524862 (NUMERAL 0) term100). Qed.
Lemma lem2524864 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524865 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524866 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524865 h1) (fun h1 : term300 = True => @lem2524864)). Qed.
Lemma lem2524867 : term300 = True.
Proof. exact (EQ_MP (@lem2524866) (@lem2524864)). Qed.
Lemma lem2524868 : term299 = True.
Proof. exact (TRANS (@lem2524863) (@lem2524867)). Qed.
Lemma lem2524869 : True = term299.
Proof. exact (SYM (@lem2524868)). Qed.
Lemma lem2524870 : term299.
Proof. exact (EQ_MP (@lem2524869) (@lem0)). Qed.
Lemma lem2524871 : term342.
Proof. exact (@lem2524860 (@lem2524870)). Qed.
Lemma lem2524873 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524874 : term299 = term300.
Proof. exact (@lem2524873 (NUMERAL 0) term100). Qed.
Lemma lem2524875 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524876 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524877 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524876 h1) (fun h1 : term300 = True => @lem2524875)). Qed.
Lemma lem2524878 : term300 = True.
Proof. exact (EQ_MP (@lem2524877) (@lem2524875)). Qed.
Lemma lem2524879 : term299 = True.
Proof. exact (TRANS (@lem2524874) (@lem2524878)). Qed.
Lemma lem2524880 : True = term299.
Proof. exact (SYM (@lem2524879)). Qed.
Lemma lem2524881 : term299.
Proof. exact (EQ_MP (@lem2524880) (@lem0)). Qed.
Lemma lem2524882 : term343.
Proof. exact (@lem2524871 (@lem2524881)). Qed.
Lemma lem2524884 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524885 : term299 = term300.
Proof. exact (@lem2524884 (NUMERAL 0) term100). Qed.
Lemma lem2524886 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524887 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524888 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524887 h1) (fun h1 : term300 = True => @lem2524886)). Qed.
Lemma lem2524889 : term300 = True.
Proof. exact (EQ_MP (@lem2524888) (@lem2524886)). Qed.
Lemma lem2524890 : term299 = True.
Proof. exact (TRANS (@lem2524885) (@lem2524889)). Qed.
Lemma lem2524891 : True = term299.
Proof. exact (SYM (@lem2524890)). Qed.
Lemma lem2524892 : term299.
Proof. exact (EQ_MP (@lem2524891) (@lem0)). Qed.
Lemma lem2524893 : term344.
Proof. exact (@lem2524882 (@lem2524892)). Qed.
Lemma lem2524895 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524896 : term196 = term197.
Proof. exact (@lem2524895 term100 term100). Qed.
Lemma lem2524897 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524898 : term199 = term100.
Proof. exact (EQ_MP (@lem2524897) (@lem940073)). Qed.
Lemma lem2524899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524900 : term197 = term99.
Proof. exact (MK_COMB (@lem2524899) (@lem2524898)). Qed.
Lemma lem2524901 : term196 = term99.
Proof. exact (TRANS (@lem2524896) (@lem2524900)). Qed.
Lemma lem2524903 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2524904 : term191 = term202.
Proof. exact (@lem2524903 term100 term100). Qed.
Lemma lem2524905 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524906 : term199 = term100.
Proof. exact (EQ_MP (@lem2524905) (@lem940073)). Qed.
Lemma lem2524907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524908 : term197 = term99.
Proof. exact (MK_COMB (@lem2524907) (@lem2524906)). Qed.
Lemma lem2524909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2524910 : term202 = term183.
Proof. exact (MK_COMB (@lem2524909) (@lem2524908)). Qed.
Lemma lem2524911 : term191 = term183.
Proof. exact (TRANS (@lem2524904) (@lem2524910)). Qed.
Lemma lem2524912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524913 : term345 = term337.
Proof. exact (MK_COMB (@lem2524912) (@lem2524911)). Qed.
Lemma lem2524914 : term346 = term339.
Proof. exact (MK_COMB (@lem2524913) (@lem2524901)). Qed.
Lemma lem2524916 (m : nat) : (term347 m) = term106.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2524917 : term339 = term106.
Proof. exact (@lem2524916 term100). Qed.
Lemma lem2524918 : term346 = term106.
Proof. exact (TRANS (@lem2524914) (@lem2524917)). Qed.
Lemma lem2524919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2524920 : term348 = term134.
Proof. exact (MK_COMB (@lem2524919) (@lem2524918)). Qed.
Lemma lem2524921 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2524922 : term349 = term305.
Proof. exact (MK_COMB (@lem2524920) (@lem2524921)). Qed.
Lemma lem2524924 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524925 : term305 = term106.
Proof. exact (@lem2524924 term100). Qed.
Lemma lem2524926 : term349 = term106.
Proof. exact (TRANS (@lem2524922) (@lem2524925)). Qed.
Lemma lem2524928 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2524929 : term196 = term197.
Proof. exact (@lem2524928 term100 term100). Qed.
Lemma lem2524930 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2524931 : term199 = term100.
Proof. exact (EQ_MP (@lem2524930) (@lem940073)). Qed.
Lemma lem2524932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2524933 : term197 = term99.
Proof. exact (MK_COMB (@lem2524932) (@lem2524931)). Qed.
Lemma lem2524934 : term196 = term99.
Proof. exact (TRANS (@lem2524929) (@lem2524933)). Qed.
Lemma lem2524935 : term134 = term134.
Proof. exact (eq_refl term134). Qed.
Lemma lem2524936 : term350 = term305.
Proof. exact (MK_COMB (@lem2524935) (@lem2524934)). Qed.
Lemma lem2524938 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2524939 : term305 = term106.
Proof. exact (@lem2524938 term100). Qed.
Lemma lem2524940 : term350 = term106.
Proof. exact (TRANS (@lem2524936) (@lem2524939)). Qed.
Lemma lem2524941 : term106 = term350.
Proof. exact (SYM (@lem2524940)). Qed.
Lemma lem2524942 : term349 = term350.
Proof. exact (TRANS (@lem2524926) (@lem2524941)). Qed.
Lemma lem2524943 : term340 = term293.
Proof. exact (@lem2524893 (@lem2524942)). Qed.
Lemma lem2524944 : term339 = term293.
Proof. exact (TRANS (@lem2524859) (@lem2524943)). Qed.
Lemma lem2524946 (x : real) : (term205 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2524947 : term293 = term106.
Proof. exact (@lem2524946 term106). Qed.
Lemma lem2524948 : term339 = term106.
Proof. exact (TRANS (@lem2524944) (@lem2524947)). Qed.
Lemma lem2524949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2524950 : term351 = term134.
Proof. exact (MK_COMB (@lem2524949) (@lem2524948)). Qed.
Lemma lem2524951 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2524952 (n : int) : (term336 n) = (term135 n).
Proof. exact (MK_COMB (@lem2524950) (@lem2524951 n)). Qed.
Lemma lem2524953 (n : int) : (term335 n) = (term135 n).
Proof. exact (TRANS (@lem2524850 n) (@lem2524952 n)). Qed.
Lemma lem2524954 (n : int) : (term135 n) = term106.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2524955 (n : int) : (term335 n) = term106.
Proof. exact (TRANS (@lem2524953 n) (@lem2524954 n)). Qed.
Lemma lem2524956 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2524957 (n : int) : (term352 n) = term116.
Proof. exact (MK_COMB (@lem2524956) (@lem2524955 n)). Qed.
Lemma lem2524958 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem2524959 (n : int) : (term333 n) = term230.
Proof. exact (MK_COMB (@lem2524957 n) (@lem2524958)). Qed.
Lemma lem2524960 (n : int) : (term369 n) = term230.
Proof. exact (TRANS (@lem2524849 n) (@lem2524959 n)). Qed.
Lemma lem2524961 : term230 = term183.
Proof. exact (@lem1982721 term183). Qed.
Lemma lem2524962 (n : int) : (term369 n) = term183.
Proof. exact (TRANS (@lem2524960 n) (@lem2524961)). Qed.
Lemma lem2524963 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2524964 (n : int) : (term370 n) = term232.
Proof. exact (MK_COMB (@lem2524963) (@lem2524962 n)). Qed.
Lemma lem2524965 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem2524966 (n : int) : (term368 n) = term233.
Proof. exact (MK_COMB (@lem2524964 n) (@lem2524965)). Qed.
Lemma lem2524967 (n : int) (h1 : term285 n) : term233.
Proof. exact (EQ_MP (@lem2524966 n) (@lem2524848 n h1)). Qed.
Lemma lem2524969 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2524970 : term233 = term292.
Proof. exact (@lem2524969 term106 term183). Qed.
Lemma lem2524972 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2524973 : term183 = term188.
Proof. exact (@lem2524972 term100). Qed.
Lemma lem2524975 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2524976 : term106 = term293.
Proof. exact (@lem2524975 (NUMERAL 0)). Qed.
Lemma lem2524977 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2524978 : term294 = term295.
Proof. exact (MK_COMB (@lem2524977) (@lem2524976)). Qed.
Lemma lem2524979 : term292 = term296.
Proof. exact (MK_COMB (@lem2524978) (@lem2524973)). Qed.
Lemma lem2524980 : term297.
Proof. exact (@lem1980026 term106 term99 term183 term99). Qed.
Lemma lem2524982 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524983 : term299 = term300.
Proof. exact (@lem2524982 (NUMERAL 0) term100). Qed.
Lemma lem2524984 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524985 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524986 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524985 h1) (fun h1 : term300 = True => @lem2524984)). Qed.
Lemma lem2524987 : term300 = True.
Proof. exact (EQ_MP (@lem2524986) (@lem2524984)). Qed.
Lemma lem2524988 : term299 = True.
Proof. exact (TRANS (@lem2524983) (@lem2524987)). Qed.
Lemma lem2524989 : True = term299.
Proof. exact (SYM (@lem2524988)). Qed.
Lemma lem2524990 : term299.
Proof. exact (EQ_MP (@lem2524989) (@lem0)). Qed.
Lemma lem2524991 : term302.
Proof. exact (@lem2524980 (@lem2524990)). Qed.
Lemma lem2524993 (m : nat) (n : nat) : (term298 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2524994 : term299 = term300.
Proof. exact (@lem2524993 (NUMERAL 0) term100). Qed.
Lemma lem2524995 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2524996 (h1 : term301 = (BIT1 0)) : term300 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2524997 : (term301 = (BIT1 0)) = (term300 = True).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2524996 h1) (fun h1 : term300 = True => @lem2524995)). Qed.
Lemma lem2524998 : term300 = True.
Proof. exact (EQ_MP (@lem2524997) (@lem2524995)). Qed.
Lemma lem2524999 : term299 = True.
Proof. exact (TRANS (@lem2524994) (@lem2524998)). Qed.
Lemma lem2525000 : True = term299.
Proof. exact (SYM (@lem2524999)). Qed.
Lemma lem2525001 : term299.
Proof. exact (EQ_MP (@lem2525000) (@lem0)). Qed.
Lemma lem2525002 : term296 = term303.
Proof. exact (@lem2524991 (@lem2525001)). Qed.
Lemma lem2525004 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2525005 : term191 = term202.
Proof. exact (@lem2525004 term100 term100). Qed.
Lemma lem2525006 : (term198 = (BIT1 0)) = (term199 = term100).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2525007 : term199 = term100.
Proof. exact (EQ_MP (@lem2525006) (@lem940073)). Qed.
Lemma lem2525008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2525009 : term197 = term99.
Proof. exact (MK_COMB (@lem2525008) (@lem2525007)). Qed.
Lemma lem2525010 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2525011 : term202 = term183.
Proof. exact (MK_COMB (@lem2525010) (@lem2525009)). Qed.
Lemma lem2525012 : term191 = term183.
Proof. exact (TRANS (@lem2525005) (@lem2525011)). Qed.
Lemma lem2525014 (x : nat) : (term304 x) = term106.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2525015 : term305 = term106.
Proof. exact (@lem2525014 term100). Qed.
Lemma lem2525016 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2525017 : term306 = term294.
Proof. exact (MK_COMB (@lem2525016) (@lem2525015)). Qed.
Lemma lem2525018 : term303 = term292.
Proof. exact (MK_COMB (@lem2525017) (@lem2525012)). Qed.
Lemma lem2525020 (m : nat) (n : nat) : (term307 m n) = (term308 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2525021 : term292 = term309.
Proof. exact (@lem2525020 (NUMERAL 0) term100). Qed.
Lemma lem2525022 : term301 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2525023 (h1 : term301 = (BIT1 0)) : (term100 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2525024 : (term301 = (BIT1 0)) = ((term100 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term301 = (BIT1 0) => @lem2525023 h1) (fun h1 : (term100 = (NUMERAL 0)) = False => @lem2525022)). Qed.
Lemma lem2525025 : (term100 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2525024) (@lem2525022)). Qed.
Lemma lem2525026 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2525027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2525028 : term310 = (and True).
Proof. exact (MK_COMB (@lem2525027) (@lem2525026)). Qed.
Lemma lem2525029 : term309 = (True /\ False).
Proof. exact (MK_COMB (@lem2525028) (@lem2525025)). Qed.
Lemma lem2525031 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2525032 : term309 = False.
Proof. exact (TRANS (@lem2525029) (@lem2525031)). Qed.
Lemma lem2525033 : term292 = False.
Proof. exact (TRANS (@lem2525021) (@lem2525032)). Qed.
Lemma lem2525034 : term303 = False.
Proof. exact (TRANS (@lem2525018) (@lem2525033)). Qed.
Lemma lem2525035 : term296 = False.
Proof. exact (TRANS (@lem2525002) (@lem2525034)). Qed.
Lemma lem2525036 : term292 = False.
Proof. exact (TRANS (@lem2524979) (@lem2525035)). Qed.
Lemma lem2525037 : term233 = False.
Proof. exact (TRANS (@lem2524970) (@lem2525036)). Qed.
Lemma lem2525038 (n : int) (h1 : term285 n) : False.
Proof. exact (EQ_MP (@lem2525037) (@lem2524967 n h1)). Qed.
Lemma lem2525039 (n : int) (h1 : term288 n) : False.
Proof. exact (or_elim (@lem2524342 n h1) (fun h0 : term282 n => @lem2524690 n h0) (fun h0 : term285 n => @lem2525038 n h0)). Qed.
Lemma lem2525040 (n : int) (h1 : term289 n) : False.
Proof. exact (or_elim (@lem2524191 n h1) (fun h0 : term260 n => @lem2524341 n h0) (fun h0 : term288 n => @lem2525039 n h0)). Qed.
Lemma lem2525041 (n : int) (h1 : term290 n) : False.
Proof. exact (or_elim (@lem2523888 n h1) (fun h0 : term266 n => @lem2524190 n h0) (fun h0 : term289 n => @lem2525040 n h0)). Qed.
Lemma lem2525042 (n : int) (h1 : term269 n) : term269 n.
Proof. exact (h1). Qed.
Lemma lem2525043 (n : int) (h1 : term269 n) : term290 n.
Proof. exact (EQ_MP (@lem2523887 n) (@lem2525042 n h1)). Qed.
Lemma lem2525044 (n : int) (h1 : term269 n) : (term290 n) = False.
Proof. exact (prop_ext (fun h2 : term290 n => @lem2525041 n h2) (fun h2 : False => @lem2525043 n h1)). Qed.
Lemma lem2525045 (n : int) (h1 : term269 n) : False.
Proof. exact (EQ_MP (@lem2525044 n h1) (@lem2525043 n h1)). Qed.
Lemma lem2525046 (n : int) (h1 : term177 n) : term177 n.
Proof. exact (h1). Qed.
Lemma lem2525047 (n : int) (h1 : term177 n) : term269 n.
Proof. exact (EQ_MP (@lem2523782 n) (@lem2525046 n h1)). Qed.
Lemma lem2525048 (n : int) (h1 : term177 n) : (term269 n) = False.
Proof. exact (prop_ext (fun h2 : term269 n => @lem2525045 n h2) (fun h2 : False => @lem2525047 n h1)). Qed.
Lemma lem2525049 (n : int) (h1 : term177 n) : False.
Proof. exact (EQ_MP (@lem2525048 n h1) (@lem2525047 n h1)). Qed.
Lemma lem2525050 (n : int) : term371 n.
Proof. exact (fun h0 : term177 n => @lem2525049 n h0). Qed.
Lemma lem2525051 (n : int) : term372 n.
Proof. exact (@lem1386578 (term373 n)). Qed.
Lemma lem2525054 (n : int) : term373 n.
Proof. exact (@lem2525051 n (@lem2525050 n)). Qed.
Lemma lem2525055 (n : int) : (term175 n) = (term83 n).
Proof. exact (SYM (@lem2523278 n)). Qed.
Lemma lem2525056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2525057 (n : int) : (term373 n) = (term68 n).
Proof. exact (MK_COMB (@lem2525056) (@lem2525055 n)). Qed.
Lemma lem2525058 (n : int) : term68 n.
Proof. exact (EQ_MP (@lem2525057 n) (@lem2525054 n)). Qed.
Lemma lem2525059 (n : int) : term69 n.
Proof. exact (EQ_MP (@lem2523035 n) (@lem2525058 n)). Qed.
Lemma lem2525060 (n : int) : (term69 n) = ((term69 n) = True).
Proof. exact (@lem7 (term69 n)). Qed.
Lemma lem2525061 (n : int) : (term69 n) = True.
Proof. exact (EQ_MP (@lem2525060 n) (@lem2525059 n)). Qed.
Lemma lem2525062 (n : int) : True = (term69 n).
Proof. exact (SYM (@lem2525061 n)). Qed.
Lemma lem2525063 (n : int) : term69 n.
Proof. exact (EQ_MP (@lem2525062 n) (@lem0)). Qed.
Lemma lem2525064 (n : int) (h1 : term22 n) : term84 n.
Proof. exact (@lem2525063 n (@lem2522905 n h1)). Qed.
Lemma lem2525066 (n : int) (h1 : term22 n) : term52 n.
Proof. exact (@lem2523034 n (@lem2525064 n h1)). Qed.
Lemma lem2525067 (n : int) : term52 n.
Proof. exact (or_elim (@lem2522903 n) (fun h0 : n = term20 => @lem2523004 n h0) (fun h0 : term22 n => @lem2525066 n h0)). Qed.
Lemma lem2525072 : term55.
Proof. exact (fun n : int => @lem2525067 n). Qed.
Lemma lem2525073 : term46.
Proof. exact (EQ_MP (@lem2522949) (@lem2525072)). Qed.
