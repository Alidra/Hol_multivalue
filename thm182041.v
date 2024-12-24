Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm182041_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import AND_FORALL_THM_spec.
Require Import DIVMOD_UNIQ_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80360_spec.
Require Import thm89994_spec.
Lemma lem181827 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem181828 (m : nat) : term1 m.
Proof. exact (@lem181827 m). Qed.
Lemma lem181829 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem181830 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem181829 m) (@lem181828 m)). Qed.
Lemma lem181831 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem181830 m n). Qed.
Lemma lem181832 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem181834 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem181835 (m : nat) : term7 m.
Proof. exact (@lem181834 m). Qed.
Lemma lem181836 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem181838 : term9.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem181854 : term10.
Proof. exact (proj1 (@lem181838)). Qed.
Lemma lem181855 (m : nat) : term11 m.
Proof. exact (@lem181854 m). Qed.
Lemma lem181856 (m : nat) : (term11 m) = ((term12 m) = m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem181862 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem181863 : term14.
Proof. exact (proj2 (@lem181862)). Qed.
Lemma lem181864 : term15.
Proof. exact (proj2 (@lem181863)). Qed.
Lemma lem181880 : term16.
Proof. exact (proj1 (@lem181864)). Qed.
Lemma lem181881 (m : nat) : term17 m.
Proof. exact (@lem181880 m). Qed.
Lemma lem181882 (m : nat) : (term17 m) = ((term18 m) = m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem181896 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem181897 (m : nat) (h1 : term19) : term20 m.
Proof. exact (@lem181896 h1 m). Qed.
Lemma lem181898 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem181899 (m : nat) (h1 : term19) : term21 m.
Proof. exact (EQ_MP (@lem181898 m) (@lem181897 m h1)). Qed.
Lemma lem181900 (m : nat) (n : nat) (h1 : term19) : term22 m n.
Proof. exact (@lem181899 m h1 n). Qed.
Lemma lem181901 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem181902 (m : nat) (n : nat) (h1 : term19) : term23 m n.
Proof. exact (EQ_MP (@lem181901 m n) (@lem181900 m n h1)). Qed.
Lemma lem181903 (m : nat) (n : nat) (q : nat) (h1 : term19) : term24 m n q.
Proof. exact (@lem181902 m n h1 q). Qed.
Lemma lem181904 (q : nat) (m : nat) (n : nat) : (term24 m n q) = (term25 q m n).
Proof. exact (eq_refl (term24 m n q)). Qed.
Lemma lem181905 (q : nat) (m : nat) (n : nat) (h1 : term19) : term25 q m n.
Proof. exact (EQ_MP (@lem181904 q m n) (@lem181903 m n q h1)). Qed.
Lemma lem181906 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term19) : term26 q m n r.
Proof. exact (@lem181905 q m n h1 r). Qed.
Lemma lem181907 (q : nat) (m : nat) (n : nat) (r : nat) : (term26 q m n r) = (term27 q m n r).
Proof. exact (eq_refl (term26 q m n r)). Qed.
Lemma lem181908 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term19) : term27 q m n r.
Proof. exact (EQ_MP (@lem181907 q m n r) (@lem181906 q m n r h1)). Qed.
Lemma lem181909 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term28 m q r n) : term28 m q r n.
Proof. exact (h1). Qed.
Lemma lem181910 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term19) (h2 : term28 m q r n) : term29 q m n r.
Proof. exact (@lem181908 q m n r h1 (@lem181909 m q r n h2)). Qed.
Lemma lem181911 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term28 m q r n) : term30 q m n r.
Proof. exact (fun h0 : term19 => @lem181910 m q r n h0 h1). Qed.
Lemma lem181912 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem181913 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term19) (h2 : term28 m q r n) : term29 q m n r.
Proof. exact (@lem181911 m q r n h2 (@lem181912 h1)). Qed.
Lemma lem181914 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term19) : term27 q m n r.
Proof. exact (fun h0 : term28 m q r n => @lem181913 m q r n h1 h0). Qed.
Lemma lem181915 (q : nat) (m : nat) (n : nat) (h1 : term19) : term25 q m n.
Proof. exact (fun r : nat => @lem181914 q m n r h1). Qed.
Lemma lem181916 (q : nat) (m : nat) (h1 : term19) : term31 q m.
Proof. exact (fun n : nat => @lem181915 q m n h1). Qed.
Lemma lem181917 (q : nat) (h1 : term19) : term32 q.
Proof. exact (fun m : nat => @lem181916 q m h1). Qed.
Lemma lem181918 (h1 : term19) : term33.
Proof. exact (fun q : nat => @lem181917 q h1). Qed.
Lemma lem181919 : term34.
Proof. exact (fun h0 : term19 => @lem181918 h0). Qed.
Lemma lem181920 : term33.
Proof. exact (@lem181919 (@lem169651)). Qed.
Lemma lem181921 (q : nat) : term35 q.
Proof. exact (@lem181920 q). Qed.
Lemma lem181922 (q : nat) : (term35 q) = (term32 q).
Proof. exact (eq_refl (term35 q)). Qed.
Lemma lem181923 (q : nat) : term32 q.
Proof. exact (EQ_MP (@lem181922 q) (@lem181921 q)). Qed.
Lemma lem181924 (q : nat) (m : nat) : term36 q m.
Proof. exact (@lem181923 q m). Qed.
Lemma lem181925 (q : nat) (m : nat) : (term36 q m) = (term31 q m).
Proof. exact (eq_refl (term36 q m)). Qed.
Lemma lem181926 (q : nat) (m : nat) : term31 q m.
Proof. exact (EQ_MP (@lem181925 q m) (@lem181924 q m)). Qed.
Lemma lem181927 (q : nat) (m : nat) (n : nat) : term37 q m n.
Proof. exact (@lem181926 q m n). Qed.
Lemma lem181928 (q : nat) (m : nat) (n : nat) : (term37 q m n) = (term25 q m n).
Proof. exact (eq_refl (term37 q m n)). Qed.
Lemma lem181929 (q : nat) (m : nat) (n : nat) : term25 q m n.
Proof. exact (EQ_MP (@lem181928 q m n) (@lem181927 q m n)). Qed.
Lemma lem181930 (q : nat) (m : nat) (n : nat) (r : nat) : term26 q m n r.
Proof. exact (@lem181929 q m n r). Qed.
Lemma lem181931 (q : nat) (m : nat) (n : nat) (r : nat) : (term26 q m n r) = (term27 q m n r).
Proof. exact (eq_refl (term26 q m n r)). Qed.
Lemma lem181933 {A : Type'} (P : A -> Prop) : term38 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem181934 {A : Type'} (P : A -> Prop) : (term38 A P) = (term39 A P).
Proof. exact (eq_refl (term38 A P)). Qed.
Lemma lem181935 {A : Type'} (P : A -> Prop) : term39 A P.
Proof. exact (EQ_MP (@lem181934 A P) (@lem181933 A P)). Qed.
Lemma lem181936 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term40 A P Q.
Proof. exact (@lem181935 A P Q). Qed.
Lemma lem181937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term40 A P Q) = ((term41 A P Q) = (term42 A P Q)).
Proof. exact (eq_refl (term40 A P Q)). Qed.
Lemma lem181940 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem181937 A P Q) (@lem181936 A P Q)). Qed.
Lemma lem181941 (P : nat -> Prop) (Q : nat -> Prop) : (term43 P Q) = (term44 P Q).
Proof. exact (@lem181940 nat P Q). Qed.
Lemma lem181942 : term45 = term46.
Proof. exact (@lem181941 term47 term48). Qed.
Lemma lem181943 (n : nat) : (term49 n) = ((term50 n) = n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem181944 : term51 = term47.
Proof. exact (fun_ext (fun n : nat => @lem181943 n)). Qed.
Lemma lem181945 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem181946 : term52 = term53.
Proof. exact (MK_COMB (@lem181945) (@lem181944)). Qed.
Lemma lem181947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181948 : term54 = term55.
Proof. exact (MK_COMB (@lem181947) (@lem181946)). Qed.
Lemma lem181949 (n : nat) : (term56 n) = ((term57 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem181950 : term58 = term48.
Proof. exact (fun_ext (fun n : nat => @lem181949 n)). Qed.
Lemma lem181951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem181952 : term59 = term60.
Proof. exact (MK_COMB (@lem181951) (@lem181950)). Qed.
Lemma lem181953 : term45 = term61.
Proof. exact (MK_COMB (@lem181948) (@lem181952)). Qed.
Lemma lem181954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem181955 : term62 = term63.
Proof. exact (MK_COMB (@lem181954) (@lem181953)). Qed.
Lemma lem181956 (n : nat) : (term49 n) = ((term50 n) = n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem181957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181958 (n : nat) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem181957) (@lem181956 n)). Qed.
Lemma lem181959 (n : nat) : (term56 n) = ((term57 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem181960 (n : nat) : (term66 n) = (term67 n).
Proof. exact (MK_COMB (@lem181958 n) (@lem181959 n)). Qed.
Lemma lem181961 : term68 = term69.
Proof. exact (fun_ext (fun n : nat => @lem181960 n)). Qed.
Lemma lem181962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem181963 : term46 = term70.
Proof. exact (MK_COMB (@lem181962) (@lem181961)). Qed.
Lemma lem181964 : (term45 = term46) = (term61 = term70).
Proof. exact (MK_COMB (@lem181955) (@lem181963)). Qed.
Lemma lem181965 : term61 = term70.
Proof. exact (EQ_MP (@lem181964) (@lem181942)). Qed.
Lemma lem181976 : term70 = term61.
Proof. exact (SYM (@lem181965)). Qed.
Lemma lem181978 (q : nat) (m : nat) (n : nat) (r : nat) : term27 q m n r.
Proof. exact (EQ_MP (@lem181931 q m n r) (@lem181930 q m n r)). Qed.
Lemma lem181979 (n : nat) : term71 n.
Proof. exact (@lem181978 n n term72 (NUMERAL 0)). Qed.
Lemma lem181985 (m : nat) : (term12 m) = m.
Proof. exact (EQ_MP (@lem181856 m) (@lem181855 m)). Qed.
Lemma lem181986 (n : nat) : (term73 n) = (term18 n).
Proof. exact (@lem181985 (term18 n)). Qed.
Lemma lem181988 (m : nat) : (term18 m) = m.
Proof. exact (EQ_MP (@lem181882 m) (@lem181881 m)). Qed.
Lemma lem181989 (n : nat) : (term18 n) = n.
Proof. exact (@lem181988 n). Qed.
Lemma lem181990 (n : nat) : (term73 n) = n.
Proof. exact (TRANS (@lem181986 n) (@lem181989 n)). Qed.
Lemma lem181991 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem181992 (n : nat) : (n = (term73 n)) = (n = n).
Proof. exact (MK_COMB (@lem181991 n) (@lem181990 n)). Qed.
Lemma lem181994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem181995 (x : nat) : (x = x) = True.
Proof. exact (@lem181994 nat x). Qed.
Lemma lem181996 (n : nat) : (n = n) = True.
Proof. exact (@lem181995 n). Qed.
Lemma lem181997 (n : nat) : (n = (term73 n)) = True.
Proof. exact (TRANS (@lem181992 n) (@lem181996 n)). Qed.
Lemma lem181998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem181999 (n : nat) : (term74 n) = (and True).
Proof. exact (MK_COMB (@lem181998) (@lem181997 n)). Qed.
Lemma lem182000 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem182001 (n : nat) : (term76 n) = term77.
Proof. exact (MK_COMB (@lem181999 n) (@lem182000)). Qed.
Lemma lem182003 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem182004 : term77 = term75.
Proof. exact (@lem182003 term75). Qed.
Lemma lem182005 (n : nat) : (term76 n) = term75.
Proof. exact (TRANS (@lem182001 n) (@lem182004)). Qed.
Lemma lem182006 (n : nat) : term75 = (term76 n).
Proof. exact (SYM (@lem182005 n)). Qed.
Lemma lem182008 : term72 = term78.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem182009 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem182010 : term75 = term80.
Proof. exact (MK_COMB (@lem182009) (@lem182008)). Qed.
Lemma lem182012 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem181832 m n) (@lem181831 m n)). Qed.
Lemma lem182013 : term80 = term81.
Proof. exact (@lem182012 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem182017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182018 (x : nat) : (x = x) = True.
Proof. exact (@lem182017 nat x). Qed.
Lemma lem182019 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem182018 (NUMERAL 0)). Qed.
Lemma lem182020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem182021 : term82 = (or True).
Proof. exact (MK_COMB (@lem182020) (@lem182019)). Qed.
Lemma lem182023 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem181836 m) (@lem181835 m)). Qed.
Lemma lem182024 : term83 = False.
Proof. exact (@lem182023 (NUMERAL 0)). Qed.
Lemma lem182025 : term81 = (True \/ False).
Proof. exact (MK_COMB (@lem182021) (@lem182024)). Qed.
Lemma lem182027 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem182028 : (True \/ False) = True.
Proof. exact (@lem182027 False). Qed.
Lemma lem182029 : term81 = True.
Proof. exact (TRANS (@lem182025) (@lem182028)). Qed.
Lemma lem182030 : term80 = True.
Proof. exact (TRANS (@lem182013) (@lem182029)). Qed.
Lemma lem182031 : term75 = True.
Proof. exact (TRANS (@lem182010) (@lem182030)). Qed.
Lemma lem182032 : True = term75.
Proof. exact (SYM (@lem182031)). Qed.
Lemma lem182033 : term75.
Proof. exact (EQ_MP (@lem182032) (@lem0)). Qed.
Lemma lem182034 (n : nat) : term76 n.
Proof. exact (EQ_MP (@lem182006 n) (@lem182033)). Qed.
Lemma lem182035 (n : nat) : term67 n.
Proof. exact (@lem181979 n (@lem182034 n)). Qed.
Lemma lem182040 : term70.
Proof. exact (fun n : nat => @lem182035 n). Qed.
Lemma lem182041 : term61.
Proof. exact (EQ_MP (@lem181976) (@lem182040)). Qed.
