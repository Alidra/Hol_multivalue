Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_LEX_DEPENDENT_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem361748 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term0 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem361749 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
Lemma lem361751 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem361752 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem361753 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (EQ_MP (@lem361752 A P) (@lem361751 A P)). Qed.
Lemma lem361754 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (@lem361753 A P Q). Qed.
Lemma lem361755 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem361757 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem361758 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem361759 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (EQ_MP (@lem361758 A P) (@lem361757 A P)). Qed.
Lemma lem361760 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (@lem361759 A P Q). Qed.
Lemma lem361761 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem361763 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term0 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem361764 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
Lemma lem361766 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem361767 {A : Type'} (P : A -> Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem361768 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (EQ_MP (@lem361767 A P) (@lem361766 A P)). Qed.
Lemma lem361769 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (@lem361768 A P Q). Qed.
Lemma lem361770 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem361772 {A : Type'} (lt2 : type1402 A) : term8 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem361773 {A : Type'} (lt2 : type1402 A) : (term8 A lt2) = ((@WF A lt2) = (term9 A lt2)).
Proof. exact (eq_refl (term8 A lt2)). Qed.
Lemma lem361780 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term9 A lt2).
Proof. exact (EQ_MP (@lem361773 A lt2) (@lem361772 A lt2)). Qed.
Lemma lem361781 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term9 A lt2).
Proof. exact (@lem361780 A lt2). Qed.
Lemma lem361782 {A : Type'} (R : type1402 A) : (@WF A R) = (term9 A R).
Proof. exact (@lem361781 A R). Qed.
Lemma lem361805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem361806 {A : Type'} (R : type1402 A) : (term10 A R) = (term11 A R).
Proof. exact (MK_COMB (@lem361805) (@lem361782 A R)). Qed.
Lemma lem361812 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term9 A lt2).
Proof. exact (EQ_MP (@lem361773 A lt2) (@lem361772 A lt2)). Qed.
Lemma lem361813 {B : Type'} (lt2 : type1402 B) : (@WF B lt2) = (term9 B lt2).
Proof. exact (@lem361812 B lt2). Qed.
Lemma lem361814 {A B : Type'} (S' : type1406 A B) (a : A) : (term12 A B S' a) = (term13 A B S' a).
Proof. exact (@lem361813 B (S' a)). Qed.
Lemma lem361837 {A B : Type'} (S' : type1406 A B) : (term14 A B S') = (term15 A B S').
Proof. exact (fun_ext (fun a : A => @lem361814 A B S' a)). Qed.
Lemma lem361838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem361839 {A B : Type'} (S' : type1406 A B) : (term16 A B S') = (term17 A B S').
Proof. exact (MK_COMB (@lem361838 A) (@lem361837 A B S')). Qed.
Lemma lem361844 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term18 A B R S') = (term19 A B R S').
Proof. exact (MK_COMB (@lem361806 A R) (@lem361839 A B S')). Qed.
Lemma lem361847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem361848 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term20 A B R S') = (term21 A B R S').
Proof. exact (MK_COMB (@lem361847) (@lem361844 A B R S')). Qed.
Lemma lem361850 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term9 A lt2).
Proof. exact (EQ_MP (@lem361773 A lt2) (@lem361772 A lt2)). Qed.
Lemma lem361851 {A B : Type'} (lt2 : type1204 A B) : (@WF (prod A B) lt2) = (term22 A B lt2).
Proof. exact (@lem361850 (prod A B) lt2). Qed.
Lemma lem361852 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term23 A B R S') = (term24 A B R S').
Proof. exact (@lem361851 A B (term25 A B R S')). Qed.
Lemma lem361897 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term26 A B R S') = (term27 A B R S').
Proof. exact (MK_COMB (@lem361848 A B R S') (@lem361852 A B R S')). Qed.
Lemma lem361900 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term27 A B R S') = (term26 A B R S').
Proof. exact (SYM (@lem361897 A B R S')). Qed.
Lemma lem361901 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term19 A B R S') : term19 A B R S'.
Proof. exact (h1). Qed.
Lemma lem361902 {A B : Type'} (S' : type1406 A B) (h1 : term17 A B S') : term17 A B S'.
Proof. exact (h1). Qed.
Lemma lem361903 {A : Type'} (R : type1402 A) (h1 : term9 A R) : term9 A R.
Proof. exact (h1). Qed.
Lemma lem361905 {A : Type'} (P : A -> Prop) (Q : Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem361770 A P Q) (@lem361769 A P Q)). Qed.
Lemma lem361906 {A B : Type'} (P : type1210 A B) (Q : Prop) : (term28 A B P Q) = (term29 A B P Q).
Proof. exact (@lem361905 (prod A B) P Q). Qed.
Lemma lem361907 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term30 A B R S' P) = (term31 A B R S' P).
Proof. exact (@lem361906 A B P (term32 A B R S' P)). Qed.
Lemma lem361948 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term31 A B R S' P) = (term30 A B R S' P).
Proof. exact (SYM (@lem361907 A B R S' P)). Qed.
Lemma lem361950 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem361764 _5106 _5107 P) (@lem361763 _5106 _5107 P)). Qed.
Lemma lem361951 {A B : Type'} (P : type1210 A B) : (term33 A B P) = (term34 A B P).
Proof. exact (@lem361950 B A P). Qed.
Lemma lem361952 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term35 A B R S' P) = (term36 A B R S' P).
Proof. exact (@lem361951 A B (term37 A B R S' P)). Qed.
Lemma lem361953 {A B : Type'} (x : prod A B) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term38 A B R S' P x) = (term39 A B x R S' P).
Proof. exact (eq_refl (term38 A B R S' P x)). Qed.
Lemma lem361954 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term40 A B R S' P) = (term37 A B R S' P).
Proof. exact (fun_ext (fun x : prod A B => @lem361953 A B x R S' P)). Qed.
Lemma lem361955 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem361956 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term35 A B R S' P) = (term31 A B R S' P).
Proof. exact (MK_COMB (@lem361955 A B) (@lem361954 A B R S' P)). Qed.
Lemma lem361957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361958 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term41 A B R S' P) = (term42 A B R S' P).
Proof. exact (MK_COMB (@lem361957) (@lem361956 A B R S' P)). Qed.
Lemma lem361959 {A B : Type'} (p1 : A) (p2 : B) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term43 A B R S' P p1 p2) = (term44 A B p1 p2 R S' P).
Proof. exact (eq_refl (term43 A B R S' P p1 p2)). Qed.
Lemma lem361960 {A B : Type'} (p1 : A) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term45 A B R S' P p1) = (term46 A B p1 R S' P).
Proof. exact (fun_ext (fun p2 : B => @lem361959 A B p1 p2 R S' P)). Qed.
Lemma lem361961 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem361962 {A B : Type'} (p1 : A) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term47 A B R S' P p1) = (term48 A B p1 R S' P).
Proof. exact (MK_COMB (@lem361961 B) (@lem361960 A B p1 R S' P)). Qed.
Lemma lem361963 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term49 A B R S' P) = (term50 A B R S' P).
Proof. exact (fun_ext (fun p1 : A => @lem361962 A B p1 R S' P)). Qed.
Lemma lem361964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem361965 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term36 A B R S' P) = (term51 A B R S' P).
Proof. exact (MK_COMB (@lem361964 A) (@lem361963 A B R S' P)). Qed.
Lemma lem361966 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : ((term35 A B R S' P) = (term36 A B R S' P)) = ((term31 A B R S' P) = (term51 A B R S' P)).
Proof. exact (MK_COMB (@lem361958 A B R S' P) (@lem361965 A B R S' P)). Qed.
Lemma lem361967 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term31 A B R S' P) = (term51 A B R S' P).
Proof. exact (EQ_MP (@lem361966 A B R S' P) (@lem361952 A B R S' P)). Qed.
Lemma lem361968 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term51 A B R S' P) = (term31 A B R S' P).
Proof. exact (SYM (@lem361967 A B R S' P)). Qed.
Lemma lem361969 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : term52 A B P a0 b0.
Proof. exact (h1). Qed.
Lemma lem361970 {A B : Type'} (P : type1210 A B) (R : type1402 A) (h1 : term9 A R) : term53 A B R P.
Proof. exact (@lem361903 A R h1 (term54 A B P)). Qed.
Lemma lem361971 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term53 A B R P) = (term55 A B R P).
Proof. exact (eq_refl (term53 A B R P)). Qed.
Lemma lem361972 {A B : Type'} (P : type1210 A B) (R : type1402 A) (h1 : term9 A R) : term55 A B R P.
Proof. exact (EQ_MP (@lem361971 A B R P) (@lem361970 A B P R h1)). Qed.
Lemma lem361976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem361761 A P Q) (@lem361760 A P Q)). Qed.
Lemma lem361977 {A : Type'} (P : A -> Prop) (Q : Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (@lem361976 A P Q). Qed.
Lemma lem361978 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term55 A B R P) = (term56 A B R P).
Proof. exact (@lem361977 A (term54 A B P) (term57 A B R P)). Qed.
Lemma lem361986 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem361987 {A : Type'} (f : A -> Prop) (y : A) : (term59 A f y) = (f y).
Proof. exact (@lem361986 A Prop f y). Qed.
Lemma lem361988 {A B : Type'} (P : type1210 A B) (x : A) : (term60 A B P x) = (term61 A B P x).
Proof. exact (@lem361987 A (term54 A B P) x). Qed.
Lemma lem361989 {A B : Type'} (P : type1210 A B) (a : A) : (term61 A B P a) = (term62 A B P a).
Proof. exact (eq_refl (term61 A B P a)). Qed.
Lemma lem361990 {A B : Type'} (P : type1210 A B) : (term63 A B P) = (term54 A B P).
Proof. exact (fun_ext (fun a : A => @lem361989 A B P a)). Qed.
Lemma lem361991 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem361992 {A B : Type'} (P : type1210 A B) (x : A) : (term60 A B P x) = (term61 A B P x).
Proof. exact (MK_COMB (@lem361990 A B P) (@lem361991 A x)). Qed.
Lemma lem361993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361994 {A B : Type'} (P : type1210 A B) (x : A) : (term64 A B P x) = (term65 A B P x).
Proof. exact (MK_COMB (@lem361993) (@lem361992 A B P x)). Qed.
Lemma lem361995 {A B : Type'} (P : type1210 A B) (x : A) : (term61 A B P x) = (term62 A B P x).
Proof. exact (eq_refl (term61 A B P x)). Qed.
Lemma lem361996 {A B : Type'} (P : type1210 A B) (x : A) : ((term60 A B P x) = (term61 A B P x)) = ((term61 A B P x) = (term62 A B P x)).
Proof. exact (MK_COMB (@lem361994 A B P x) (@lem361995 A B P x)). Qed.
Lemma lem361997 {A B : Type'} (P : type1210 A B) (x : A) : (term61 A B P x) = (term62 A B P x).
Proof. exact (EQ_MP (@lem361996 A B P x) (@lem361988 A B P x)). Qed.
Lemma lem362002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362003 {A B : Type'} (P : type1210 A B) (x : A) : (term66 A B P x) = (term67 A B P x).
Proof. exact (MK_COMB (@lem362002) (@lem361997 A B P x)). Qed.
Lemma lem362011 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem362012 {A : Type'} (f : A -> Prop) (y : A) : (term59 A f y) = (f y).
Proof. exact (@lem362011 A Prop f y). Qed.
Lemma lem362013 {A B : Type'} (P : type1210 A B) (x : A) : (term60 A B P x) = (term61 A B P x).
Proof. exact (@lem362012 A (term54 A B P) x). Qed.
Lemma lem362014 {A B : Type'} (P : type1210 A B) (a : A) : (term61 A B P a) = (term62 A B P a).
Proof. exact (eq_refl (term61 A B P a)). Qed.
Lemma lem362015 {A B : Type'} (P : type1210 A B) : (term63 A B P) = (term54 A B P).
Proof. exact (fun_ext (fun a : A => @lem362014 A B P a)). Qed.
Lemma lem362016 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem362017 {A B : Type'} (P : type1210 A B) (x : A) : (term60 A B P x) = (term61 A B P x).
Proof. exact (MK_COMB (@lem362015 A B P) (@lem362016 A x)). Qed.
Lemma lem362018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362019 {A B : Type'} (P : type1210 A B) (x : A) : (term64 A B P x) = (term65 A B P x).
Proof. exact (MK_COMB (@lem362018) (@lem362017 A B P x)). Qed.
Lemma lem362020 {A B : Type'} (P : type1210 A B) (x : A) : (term61 A B P x) = (term62 A B P x).
Proof. exact (eq_refl (term61 A B P x)). Qed.
Lemma lem362021 {A B : Type'} (P : type1210 A B) (x : A) : ((term60 A B P x) = (term61 A B P x)) = ((term61 A B P x) = (term62 A B P x)).
Proof. exact (MK_COMB (@lem362019 A B P x) (@lem362020 A B P x)). Qed.
Lemma lem362022 {A B : Type'} (P : type1210 A B) (x : A) : (term61 A B P x) = (term62 A B P x).
Proof. exact (EQ_MP (@lem362021 A B P x) (@lem362013 A B P x)). Qed.
Lemma lem362027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem362028 {A B : Type'} (P : type1210 A B) (x : A) : (term68 A B P x) = (term69 A B P x).
Proof. exact (MK_COMB (@lem362027) (@lem362022 A B P x)). Qed.
Lemma lem362036 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem362037 {A : Type'} (f : A -> Prop) (y : A) : (term59 A f y) = (f y).
Proof. exact (@lem362036 A Prop f y). Qed.
Lemma lem362038 {A B : Type'} (P : type1210 A B) (y : A) : (term60 A B P y) = (term61 A B P y).
Proof. exact (@lem362037 A (term54 A B P) y). Qed.
Lemma lem362039 {A B : Type'} (P : type1210 A B) (a : A) : (term61 A B P a) = (term62 A B P a).
Proof. exact (eq_refl (term61 A B P a)). Qed.
Lemma lem362040 {A B : Type'} (P : type1210 A B) : (term63 A B P) = (term54 A B P).
Proof. exact (fun_ext (fun a : A => @lem362039 A B P a)). Qed.
Lemma lem362041 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem362042 {A B : Type'} (P : type1210 A B) (y : A) : (term60 A B P y) = (term61 A B P y).
Proof. exact (MK_COMB (@lem362040 A B P) (@lem362041 A y)). Qed.
Lemma lem362043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362044 {A B : Type'} (P : type1210 A B) (y : A) : (term64 A B P y) = (term65 A B P y).
Proof. exact (MK_COMB (@lem362043) (@lem362042 A B P y)). Qed.
Lemma lem362045 {A B : Type'} (P : type1210 A B) (y : A) : (term61 A B P y) = (term62 A B P y).
Proof. exact (eq_refl (term61 A B P y)). Qed.
Lemma lem362046 {A B : Type'} (P : type1210 A B) (y : A) : ((term60 A B P y) = (term61 A B P y)) = ((term61 A B P y) = (term62 A B P y)).
Proof. exact (MK_COMB (@lem362044 A B P y) (@lem362045 A B P y)). Qed.
Lemma lem362047 {A B : Type'} (P : type1210 A B) (y : A) : (term61 A B P y) = (term62 A B P y).
Proof. exact (EQ_MP (@lem362046 A B P y) (@lem362038 A B P y)). Qed.
Lemma lem362052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem362053 {A B : Type'} (P : type1210 A B) (y : A) : (term70 A B P y) = (term71 A B P y).
Proof. exact (MK_COMB (@lem362052) (@lem362047 A B P y)). Qed.
Lemma lem362054 {A : Type'} (R : type1402 A) (y : A) (x : A) : (term72 A R y x) = (term72 A R y x).
Proof. exact (eq_refl (term72 A R y x)). Qed.
Lemma lem362055 {A B : Type'} (R : type1402 A) (x : A) (P : type1210 A B) (y : A) : (term73 A B R x P y) = (term74 A B R x P y).
Proof. exact (MK_COMB (@lem362054 A R y x) (@lem362053 A B P y)). Qed.
Lemma lem362058 {A B : Type'} (R : type1402 A) (x : A) (P : type1210 A B) : (term75 A B R x P) = (term76 A B R x P).
Proof. exact (fun_ext (fun y : A => @lem362055 A B R x P y)). Qed.
Lemma lem362059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362060 {A B : Type'} (R : type1402 A) (x : A) (P : type1210 A B) : (term77 A B R x P) = (term78 A B R x P).
Proof. exact (MK_COMB (@lem362059 A) (@lem362058 A B R x P)). Qed.
Lemma lem362065 {A B : Type'} (R : type1402 A) (x : A) (P : type1210 A B) : (term79 A B R x P) = (term80 A B R x P).
Proof. exact (MK_COMB (@lem362028 A B P x) (@lem362060 A B R x P)). Qed.
Lemma lem362068 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term81 A B R P) = (term82 A B R P).
Proof. exact (fun_ext (fun x : A => @lem362065 A B R x P)). Qed.
Lemma lem362069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem362070 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term57 A B R P) = (term83 A B R P).
Proof. exact (MK_COMB (@lem362069 A) (@lem362068 A B R P)). Qed.
Lemma lem362075 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term84 A B x R P) = (term85 A B x R P).
Proof. exact (MK_COMB (@lem362003 A B P x) (@lem362070 A B R P)). Qed.
Lemma lem362077 {A : Type'} (P : A -> Prop) (Q : Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem361761 A P Q) (@lem361760 A P Q)). Qed.
Lemma lem362078 {B : Type'} (P : B -> Prop) (Q : Prop) : (term6 B P Q) = (term7 B P Q).
Proof. exact (@lem362077 B P Q). Qed.
Lemma lem362079 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term86 A B x R P) = (term87 A B x R P).
Proof. exact (@lem362078 B (term88 A B P x) (term83 A B R P)). Qed.
Lemma lem362080 {A B : Type'} (P : type1210 A B) (x : A) (b : B) : (term89 A B P x b) = (term52 A B P x b).
Proof. exact (eq_refl (term89 A B P x b)). Qed.
Lemma lem362081 {A B : Type'} (P : type1210 A B) (x : A) : (term90 A B P x) = (term88 A B P x).
Proof. exact (fun_ext (fun b : B => @lem362080 A B P x b)). Qed.
Lemma lem362082 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem362083 {A B : Type'} (P : type1210 A B) (x : A) : (term91 A B P x) = (term62 A B P x).
Proof. exact (MK_COMB (@lem362082 B) (@lem362081 A B P x)). Qed.
Lemma lem362084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362085 {A B : Type'} (P : type1210 A B) (x : A) : (term92 A B P x) = (term67 A B P x).
Proof. exact (MK_COMB (@lem362084) (@lem362083 A B P x)). Qed.
Lemma lem362086 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term83 A B R P) = (term83 A B R P).
Proof. exact (eq_refl (term83 A B R P)). Qed.
Lemma lem362087 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term86 A B x R P) = (term85 A B x R P).
Proof. exact (MK_COMB (@lem362085 A B P x) (@lem362086 A B R P)). Qed.
Lemma lem362088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362089 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term93 A B x R P) = (term94 A B x R P).
Proof. exact (MK_COMB (@lem362088) (@lem362087 A B x R P)). Qed.
Lemma lem362090 {A B : Type'} (P : type1210 A B) (x : A) (b : B) : (term89 A B P x b) = (term52 A B P x b).
Proof. exact (eq_refl (term89 A B P x b)). Qed.
Lemma lem362091 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362092 {A B : Type'} (P : type1210 A B) (x : A) (b : B) : (term95 A B P x b) = (term96 A B P x b).
Proof. exact (MK_COMB (@lem362091) (@lem362090 A B P x b)). Qed.
Lemma lem362093 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term83 A B R P) = (term83 A B R P).
Proof. exact (eq_refl (term83 A B R P)). Qed.
Lemma lem362094 {A B : Type'} (x : A) (b : B) (R : type1402 A) (P : type1210 A B) : (term97 A B x b R P) = (term98 A B x b R P).
Proof. exact (MK_COMB (@lem362092 A B P x b) (@lem362093 A B R P)). Qed.
Lemma lem362095 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term99 A B x R P) = (term100 A B x R P).
Proof. exact (fun_ext (fun b : B => @lem362094 A B x b R P)). Qed.
Lemma lem362096 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362097 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term87 A B x R P) = (term101 A B x R P).
Proof. exact (MK_COMB (@lem362096 B) (@lem362095 A B x R P)). Qed.
Lemma lem362098 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : ((term86 A B x R P) = (term87 A B x R P)) = ((term85 A B x R P) = (term101 A B x R P)).
Proof. exact (MK_COMB (@lem362089 A B x R P) (@lem362097 A B x R P)). Qed.
Lemma lem362099 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term85 A B x R P) = (term101 A B x R P).
Proof. exact (EQ_MP (@lem362098 A B x R P) (@lem362079 A B x R P)). Qed.
Lemma lem362126 {A B : Type'} (x : A) (R : type1402 A) (P : type1210 A B) : (term84 A B x R P) = (term101 A B x R P).
Proof. exact (TRANS (@lem362075 A B x R P) (@lem362099 A B x R P)). Qed.
Lemma lem362127 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term102 A B R P) = (term103 A B R P).
Proof. exact (fun_ext (fun x : A => @lem362126 A B x R P)). Qed.
Lemma lem362128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362129 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term56 A B R P) = (term104 A B R P).
Proof. exact (MK_COMB (@lem362128 A) (@lem362127 A B R P)). Qed.
Lemma lem362134 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term55 A B R P) = (term104 A B R P).
Proof. exact (TRANS (@lem361978 A B R P) (@lem362129 A B R P)). Qed.
Lemma lem362135 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362136 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term105 A B R P) = (term106 A B R P).
Proof. exact (MK_COMB (@lem362135) (@lem362134 A B R P)). Qed.
Lemma lem362171 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term32 A B R S' P) = (term32 A B R S' P).
Proof. exact (eq_refl (term32 A B R S' P)). Qed.
Lemma lem362172 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term107 A B R S' P) = (term108 A B R S' P).
Proof. exact (MK_COMB (@lem362136 A B R P) (@lem362171 A B R S' P)). Qed.
Lemma lem362175 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term108 A B R S' P) = (term107 A B R S' P).
Proof. exact (SYM (@lem362172 A B R S' P)). Qed.
Lemma lem362176 {A B : Type'} (R : type1402 A) (P : type1210 A B) (h1 : term104 A B R P) : term104 A B R P.
Proof. exact (h1). Qed.
Lemma lem362177 {A B : Type'} (a0 : A) (R : type1402 A) (P : type1210 A B) (h1 : term104 A B R P) : term109 A B R P a0.
Proof. exact (@lem362176 A B R P h1 a0). Qed.
Lemma lem362178 {A B : Type'} (a0 : A) (R : type1402 A) (P : type1210 A B) : (term109 A B R P a0) = (term101 A B a0 R P).
Proof. exact (eq_refl (term109 A B R P a0)). Qed.
Lemma lem362179 {A B : Type'} (a0 : A) (R : type1402 A) (P : type1210 A B) (h1 : term104 A B R P) : term101 A B a0 R P.
Proof. exact (EQ_MP (@lem362178 A B a0 R P) (@lem362177 A B a0 R P h1)). Qed.
Lemma lem362180 {A B : Type'} (a0 : A) (b0 : B) (R : type1402 A) (P : type1210 A B) (h1 : term104 A B R P) : term110 A B a0 R P b0.
Proof. exact (@lem362179 A B a0 R P h1 b0). Qed.
Lemma lem362181 {A B : Type'} (a0 : A) (b0 : B) (R : type1402 A) (P : type1210 A B) : (term110 A B a0 R P b0) = (term98 A B a0 b0 R P).
Proof. exact (eq_refl (term110 A B a0 R P b0)). Qed.
Lemma lem362182 {A B : Type'} (a0 : A) (b0 : B) (R : type1402 A) (P : type1210 A B) (h1 : term104 A B R P) : term98 A B a0 b0 R P.
Proof. exact (EQ_MP (@lem362181 A B a0 b0 R P) (@lem362180 A B a0 b0 R P h1)). Qed.
Lemma lem362191 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) : (term52 A B P a0 b0) = ((term52 A B P a0 b0) = True).
Proof. exact (@lem7 (term52 A B P a0 b0)). Qed.
Lemma lem362198 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term52 A B P a0 b0) = True.
Proof. exact (EQ_MP (@lem362191 A B P a0 b0) (@lem361969 A B P a0 b0 h1)). Qed.
Lemma lem362199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362200 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term96 A B P a0 b0) = (imp True).
Proof. exact (MK_COMB (@lem362199) (@lem362198 A B P a0 b0 h1)). Qed.
Lemma lem362221 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term83 A B R P) = (term83 A B R P).
Proof. exact (eq_refl (term83 A B R P)). Qed.
Lemma lem362222 {A B : Type'} (R : type1402 A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term98 A B a0 b0 R P) = (term111 A B R P).
Proof. exact (MK_COMB (@lem362200 A B P a0 b0 h1) (@lem362221 A B R P)). Qed.
Lemma lem362224 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem362225 {A B : Type'} (R : type1402 A) (P : type1210 A B) : (term111 A B R P) = (term83 A B R P).
Proof. exact (@lem362224 (term83 A B R P)). Qed.
Lemma lem362246 {A B : Type'} (R : type1402 A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term98 A B a0 b0 R P) = (term83 A B R P).
Proof. exact (TRANS (@lem362222 A B R P a0 b0 h1) (@lem362225 A B R P)). Qed.
Lemma lem362247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362248 {A B : Type'} (R : type1402 A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term112 A B a0 b0 R P) = (term113 A B R P).
Proof. exact (MK_COMB (@lem362247) (@lem362246 A B R P a0 b0 h1)). Qed.
Lemma lem362283 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term32 A B R S' P) = (term32 A B R S' P).
Proof. exact (eq_refl (term32 A B R S' P)). Qed.
Lemma lem362284 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term114 A B a0 b0 R S' P) = (term115 A B R S' P).
Proof. exact (MK_COMB (@lem362248 A B R P a0 b0 h1) (@lem362283 A B R S' P)). Qed.
Lemma lem362287 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : (term115 A B R S' P) = (term114 A B a0 b0 R S' P).
Proof. exact (SYM (@lem362284 A B R S' P a0 b0 h1)). Qed.
Lemma lem362288 {A B : Type'} (R : type1402 A) (P : type1210 A B) (h1 : term83 A B R P) : term83 A B R P.
Proof. exact (h1). Qed.
Lemma lem362289 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term80 A B R a P) : term80 A B R a P.
Proof. exact (h1). Qed.
Lemma lem362290 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term78 A B R a P.
Proof. exact (h1). Qed.
Lemma lem362291 {A B : Type'} (P : type1210 A B) (a : A) (h1 : term62 A B P a) : term62 A B P a.
Proof. exact (h1). Qed.
Lemma lem362292 {A B : Type'} (P : type1210 A B) (a : A) (h1 : term62 A B P a) : term62 A B P a.
Proof. exact (h1). Qed.
Lemma lem362293 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : term52 A B P a b1.
Proof. exact (h1). Qed.
Lemma lem362297 {A B : Type'} (a : A) (S' : type1406 A B) (h1 : term17 A B S') : term116 A B S' a.
Proof. exact (@lem361902 A B S' h1 a). Qed.
Lemma lem362298 {A B : Type'} (S' : type1406 A B) (a : A) : (term116 A B S' a) = (term13 A B S' a).
Proof. exact (eq_refl (term116 A B S' a)). Qed.
Lemma lem362299 {A B : Type'} (a : A) (S' : type1406 A B) (h1 : term17 A B S') : term13 A B S' a.
Proof. exact (EQ_MP (@lem362298 A B S' a) (@lem362297 A B a S' h1)). Qed.
Lemma lem362300 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (h1 : term17 A B S') : term117 A B S' P a.
Proof. exact (@lem362299 A B a S' h1 (term88 A B P a)). Qed.
Lemma lem362301 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term117 A B S' P a) = (term118 A B S' P a).
Proof. exact (eq_refl (term117 A B S' P a)). Qed.
Lemma lem362302 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (h1 : term17 A B S') : term118 A B S' P a.
Proof. exact (EQ_MP (@lem362301 A B S' P a) (@lem362300 A B P a S' h1)). Qed.
Lemma lem362306 {A : Type'} (P : A -> Prop) (Q : Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem361755 A P Q) (@lem361754 A P Q)). Qed.
Lemma lem362307 {B : Type'} (P : B -> Prop) (Q : Prop) : (term6 B P Q) = (term7 B P Q).
Proof. exact (@lem362306 B P Q). Qed.
Lemma lem362308 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term118 A B S' P a) = (term119 A B S' P a).
Proof. exact (@lem362307 B (term88 A B P a) (term120 A B S' P a)). Qed.
Lemma lem362316 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem362317 {B : Type'} (f : B -> Prop) (y : B) : (term59 B f y) = (f y).
Proof. exact (@lem362316 B Prop f y). Qed.
Lemma lem362318 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term121 A B P a x) = (term89 A B P a x).
Proof. exact (@lem362317 B (term88 A B P a) x). Qed.
Lemma lem362319 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term89 A B P a b) = (term52 A B P a b).
Proof. exact (eq_refl (term89 A B P a b)). Qed.
Lemma lem362320 {A B : Type'} (P : type1210 A B) (a : A) : (term90 A B P a) = (term88 A B P a).
Proof. exact (fun_ext (fun b : B => @lem362319 A B P a b)). Qed.
Lemma lem362321 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem362322 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term121 A B P a x) = (term89 A B P a x).
Proof. exact (MK_COMB (@lem362320 A B P a) (@lem362321 B x)). Qed.
Lemma lem362323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362324 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term122 A B P a x) = (term123 A B P a x).
Proof. exact (MK_COMB (@lem362323) (@lem362322 A B P a x)). Qed.
Lemma lem362325 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term89 A B P a x) = (term52 A B P a x).
Proof. exact (eq_refl (term89 A B P a x)). Qed.
Lemma lem362326 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : ((term121 A B P a x) = (term89 A B P a x)) = ((term89 A B P a x) = (term52 A B P a x)).
Proof. exact (MK_COMB (@lem362324 A B P a x) (@lem362325 A B P a x)). Qed.
Lemma lem362327 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term89 A B P a x) = (term52 A B P a x).
Proof. exact (EQ_MP (@lem362326 A B P a x) (@lem362318 A B P a x)). Qed.
Lemma lem362328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362329 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term95 A B P a x) = (term96 A B P a x).
Proof. exact (MK_COMB (@lem362328) (@lem362327 A B P a x)). Qed.
Lemma lem362337 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem362338 {B : Type'} (f : B -> Prop) (y : B) : (term59 B f y) = (f y).
Proof. exact (@lem362337 B Prop f y). Qed.
Lemma lem362339 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term121 A B P a x) = (term89 A B P a x).
Proof. exact (@lem362338 B (term88 A B P a) x). Qed.
Lemma lem362340 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term89 A B P a b) = (term52 A B P a b).
Proof. exact (eq_refl (term89 A B P a b)). Qed.
Lemma lem362341 {A B : Type'} (P : type1210 A B) (a : A) : (term90 A B P a) = (term88 A B P a).
Proof. exact (fun_ext (fun b : B => @lem362340 A B P a b)). Qed.
Lemma lem362342 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem362343 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term121 A B P a x) = (term89 A B P a x).
Proof. exact (MK_COMB (@lem362341 A B P a) (@lem362342 B x)). Qed.
Lemma lem362344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362345 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term122 A B P a x) = (term123 A B P a x).
Proof. exact (MK_COMB (@lem362344) (@lem362343 A B P a x)). Qed.
Lemma lem362346 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term89 A B P a x) = (term52 A B P a x).
Proof. exact (eq_refl (term89 A B P a x)). Qed.
Lemma lem362347 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : ((term121 A B P a x) = (term89 A B P a x)) = ((term89 A B P a x) = (term52 A B P a x)).
Proof. exact (MK_COMB (@lem362345 A B P a x) (@lem362346 A B P a x)). Qed.
Lemma lem362348 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term89 A B P a x) = (term52 A B P a x).
Proof. exact (EQ_MP (@lem362347 A B P a x) (@lem362339 A B P a x)). Qed.
Lemma lem362349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem362350 {A B : Type'} (P : type1210 A B) (a : A) (x : B) : (term124 A B P a x) = (term125 A B P a x).
Proof. exact (MK_COMB (@lem362349) (@lem362348 A B P a x)). Qed.
Lemma lem362358 {A B : Type'} (f : A -> B) (y : A) : (term58 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem362359 {B : Type'} (f : B -> Prop) (y : B) : (term59 B f y) = (f y).
Proof. exact (@lem362358 B Prop f y). Qed.
Lemma lem362360 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term121 A B P a y) = (term89 A B P a y).
Proof. exact (@lem362359 B (term88 A B P a) y). Qed.
Lemma lem362361 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term89 A B P a b) = (term52 A B P a b).
Proof. exact (eq_refl (term89 A B P a b)). Qed.
Lemma lem362362 {A B : Type'} (P : type1210 A B) (a : A) : (term90 A B P a) = (term88 A B P a).
Proof. exact (fun_ext (fun b : B => @lem362361 A B P a b)). Qed.
Lemma lem362363 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem362364 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term121 A B P a y) = (term89 A B P a y).
Proof. exact (MK_COMB (@lem362362 A B P a) (@lem362363 B y)). Qed.
Lemma lem362365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362366 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term122 A B P a y) = (term123 A B P a y).
Proof. exact (MK_COMB (@lem362365) (@lem362364 A B P a y)). Qed.
Lemma lem362367 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term89 A B P a y) = (term52 A B P a y).
Proof. exact (eq_refl (term89 A B P a y)). Qed.
Lemma lem362368 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : ((term121 A B P a y) = (term89 A B P a y)) = ((term89 A B P a y) = (term52 A B P a y)).
Proof. exact (MK_COMB (@lem362366 A B P a y) (@lem362367 A B P a y)). Qed.
Lemma lem362369 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term89 A B P a y) = (term52 A B P a y).
Proof. exact (EQ_MP (@lem362368 A B P a y) (@lem362360 A B P a y)). Qed.
Lemma lem362370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem362371 {A B : Type'} (P : type1210 A B) (a : A) (y : B) : (term126 A B P a y) = (term127 A B P a y).
Proof. exact (MK_COMB (@lem362370) (@lem362369 A B P a y)). Qed.
Lemma lem362372 {A B : Type'} (S' : type1406 A B) (a : A) (y : B) (x : B) : (term128 A B S' a y x) = (term128 A B S' a y x).
Proof. exact (eq_refl (term128 A B S' a y x)). Qed.
Lemma lem362373 {A B : Type'} (S' : type1406 A B) (x : B) (P : type1210 A B) (a : A) (y : B) : (term129 A B S' x P a y) = (term130 A B S' x P a y).
Proof. exact (MK_COMB (@lem362372 A B S' a y x) (@lem362371 A B P a y)). Qed.
Lemma lem362376 {A B : Type'} (S' : type1406 A B) (x : B) (P : type1210 A B) (a : A) : (term131 A B S' x P a) = (term132 A B S' x P a).
Proof. exact (fun_ext (fun y : B => @lem362373 A B S' x P a y)). Qed.
Lemma lem362377 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362378 {A B : Type'} (S' : type1406 A B) (x : B) (P : type1210 A B) (a : A) : (term133 A B S' x P a) = (term134 A B S' x P a).
Proof. exact (MK_COMB (@lem362377 B) (@lem362376 A B S' x P a)). Qed.
Lemma lem362383 {A B : Type'} (S' : type1406 A B) (x : B) (P : type1210 A B) (a : A) : (term135 A B S' x P a) = (term136 A B S' x P a).
Proof. exact (MK_COMB (@lem362350 A B P a x) (@lem362378 A B S' x P a)). Qed.
Lemma lem362386 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term137 A B S' P a) = (term138 A B S' P a).
Proof. exact (fun_ext (fun x : B => @lem362383 A B S' x P a)). Qed.
Lemma lem362387 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem362388 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term120 A B S' P a) = (term139 A B S' P a).
Proof. exact (MK_COMB (@lem362387 B) (@lem362386 A B S' P a)). Qed.
Lemma lem362393 {A B : Type'} (x : B) (S' : type1406 A B) (P : type1210 A B) (a : A) : (term140 A B x S' P a) = (term141 A B x S' P a).
Proof. exact (MK_COMB (@lem362329 A B P a x) (@lem362388 A B S' P a)). Qed.
Lemma lem362396 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term142 A B S' P a) = (term143 A B S' P a).
Proof. exact (fun_ext (fun x : B => @lem362393 A B x S' P a)). Qed.
Lemma lem362397 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362398 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term119 A B S' P a) = (term144 A B S' P a).
Proof. exact (MK_COMB (@lem362397 B) (@lem362396 A B S' P a)). Qed.
Lemma lem362403 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term118 A B S' P a) = (term144 A B S' P a).
Proof. exact (TRANS (@lem362308 A B S' P a) (@lem362398 A B S' P a)). Qed.
Lemma lem362404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362405 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term145 A B S' P a) = (term146 A B S' P a).
Proof. exact (MK_COMB (@lem362404) (@lem362403 A B S' P a)). Qed.
Lemma lem362440 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term32 A B R S' P) = (term32 A B R S' P).
Proof. exact (eq_refl (term32 A B R S' P)). Qed.
Lemma lem362441 {A B : Type'} (a : A) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term147 A B a R S' P) = (term148 A B a R S' P).
Proof. exact (MK_COMB (@lem362405 A B S' P a) (@lem362440 A B R S' P)). Qed.
Lemma lem362444 {A B : Type'} (a : A) (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term148 A B a R S' P) = (term147 A B a R S' P).
Proof. exact (SYM (@lem362441 A B a R S' P)). Qed.
Lemma lem362445 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) (h1 : term144 A B S' P a) : term144 A B S' P a.
Proof. exact (h1). Qed.
Lemma lem362446 {A B : Type'} (b1 : B) (S' : type1406 A B) (P : type1210 A B) (a : A) (h1 : term144 A B S' P a) : term149 A B S' P a b1.
Proof. exact (@lem362445 A B S' P a h1 b1). Qed.
Lemma lem362447 {A B : Type'} (b1 : B) (S' : type1406 A B) (P : type1210 A B) (a : A) : (term149 A B S' P a b1) = (term141 A B b1 S' P a).
Proof. exact (eq_refl (term149 A B S' P a b1)). Qed.
Lemma lem362448 {A B : Type'} (b1 : B) (S' : type1406 A B) (P : type1210 A B) (a : A) (h1 : term144 A B S' P a) : term141 A B b1 S' P a.
Proof. exact (EQ_MP (@lem362447 A B b1 S' P a) (@lem362446 A B b1 S' P a h1)). Qed.
Lemma lem362456 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) : (term52 A B P a b1) = ((term52 A B P a b1) = True).
Proof. exact (@lem7 (term52 A B P a b1)). Qed.
Lemma lem362463 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term52 A B P a b1) = True.
Proof. exact (EQ_MP (@lem362456 A B P a b1) (@lem362293 A B P a b1 h1)). Qed.
Lemma lem362464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362465 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term96 A B P a b1) = (imp True).
Proof. exact (MK_COMB (@lem362464) (@lem362463 A B P a b1 h1)). Qed.
Lemma lem362478 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term139 A B S' P a) = (term139 A B S' P a).
Proof. exact (eq_refl (term139 A B S' P a)). Qed.
Lemma lem362479 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term141 A B b1 S' P a) = (term150 A B S' P a).
Proof. exact (MK_COMB (@lem362465 A B P a b1 h1) (@lem362478 A B S' P a)). Qed.
Lemma lem362481 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem362482 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) : (term150 A B S' P a) = (term139 A B S' P a).
Proof. exact (@lem362481 (term139 A B S' P a)). Qed.
Lemma lem362495 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term141 A B b1 S' P a) = (term139 A B S' P a).
Proof. exact (TRANS (@lem362479 A B S' P a b1 h1) (@lem362482 A B S' P a)). Qed.
Lemma lem362496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362497 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term151 A B b1 S' P a) = (term152 A B S' P a).
Proof. exact (MK_COMB (@lem362496) (@lem362495 A B S' P a b1 h1)). Qed.
Lemma lem362532 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) : (term32 A B R S' P) = (term32 A B R S' P).
Proof. exact (eq_refl (term32 A B R S' P)). Qed.
Lemma lem362533 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term153 A B b1 a R S' P) = (term154 A B a R S' P).
Proof. exact (MK_COMB (@lem362497 A B S' P a b1 h1) (@lem362532 A B R S' P)). Qed.
Lemma lem362536 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a : A) (b1 : B) (h1 : term52 A B P a b1) : (term154 A B a R S' P) = (term153 A B b1 a R S' P).
Proof. exact (SYM (@lem362533 A B R S' P a b1 h1)). Qed.
Lemma lem362537 {A B : Type'} (S' : type1406 A B) (P : type1210 A B) (a : A) (h1 : term139 A B S' P a) : term139 A B S' P a.
Proof. exact (h1). Qed.
Lemma lem362538 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term136 A B S' b P a) : term136 A B S' b P a.
Proof. exact (h1). Qed.
Lemma lem362539 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term134 A B S' b P a.
Proof. exact (h1). Qed.
Lemma lem362540 {A B : Type'} (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : term52 A B P a b.
Proof. exact (h1). Qed.
Lemma lem362541 {A B : Type'} (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : term52 A B P a b.
Proof. exact (h1). Qed.
Lemma lem362556 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term52 A B P a b) = ((term52 A B P a b) = True).
Proof. exact (@lem7 (term52 A B P a b)). Qed.
Lemma lem362561 {A B : Type'} (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : (term52 A B P a b) = True.
Proof. exact (EQ_MP (@lem362556 A B P a b) (@lem362541 A B P a b h1)). Qed.
Lemma lem362562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem362563 {A B : Type'} (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : (term125 A B P a b) = (and True).
Proof. exact (MK_COMB (@lem362562) (@lem362561 A B P a b h1)). Qed.
Lemma lem362592 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term155 A B R S' a b P) = (term155 A B R S' a b P).
Proof. exact (eq_refl (term155 A B R S' a b P)). Qed.
Lemma lem362593 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : (term156 A B R S' a b P) = (term157 A B R S' a b P).
Proof. exact (MK_COMB (@lem362563 A B P a b h1) (@lem362592 A B R S' a b P)). Qed.
Lemma lem362595 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem362596 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term157 A B R S' a b P) = (term155 A B R S' a b P).
Proof. exact (@lem362595 (term155 A B R S' a b P)). Qed.
Lemma lem362625 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : (term156 A B R S' a b P) = (term155 A B R S' a b P).
Proof. exact (TRANS (@lem362593 A B R S' P a b h1) (@lem362596 A B R S' a b P)). Qed.
Lemma lem362626 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a : A) (b : B) (h1 : term52 A B P a b) : (term155 A B R S' a b P) = (term156 A B R S' a b P).
Proof. exact (SYM (@lem362625 A B R S' P a b h1)). Qed.
Lemma lem362632 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem361749 _5106 _5107 P) (@lem361748 _5106 _5107 P)). Qed.
Lemma lem362633 {A B : Type'} (P : type1210 A B) : (term33 A B P) = (term34 A B P).
Proof. exact (@lem362632 B A P). Qed.
Lemma lem362634 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term158 A B R S' a b P) = (term159 A B R S' a b P).
Proof. exact (@lem362633 A B (term160 A B R S' a b P)). Qed.
Lemma lem362635 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) (y : prod A B) : (term161 A B R S' a b P y) = (term162 A B R S' a b P y).
Proof. exact (eq_refl (term161 A B R S' a b P y)). Qed.
Lemma lem362636 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term163 A B R S' a b P) = (term160 A B R S' a b P).
Proof. exact (fun_ext (fun y : prod A B => @lem362635 A B R S' a b P y)). Qed.
Lemma lem362637 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem362638 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term158 A B R S' a b P) = (term155 A B R S' a b P).
Proof. exact (MK_COMB (@lem362637 A B) (@lem362636 A B R S' a b P)). Qed.
Lemma lem362639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362640 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term164 A B R S' a b P) = (term165 A B R S' a b P).
Proof. exact (MK_COMB (@lem362639) (@lem362638 A B R S' a b P)). Qed.
Lemma lem362641 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) (p1 : A) (p2 : B) : (term166 A B R S' a b P p1 p2) = (term167 A B R S' a b P p1 p2).
Proof. exact (eq_refl (term166 A B R S' a b P p1 p2)). Qed.
Lemma lem362642 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) (p1 : A) : (term168 A B R S' a b P p1) = (term169 A B R S' a b P p1).
Proof. exact (fun_ext (fun p2 : B => @lem362641 A B R S' a b P p1 p2)). Qed.
Lemma lem362643 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362644 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) (p1 : A) : (term170 A B R S' a b P p1) = (term171 A B R S' a b P p1).
Proof. exact (MK_COMB (@lem362643 B) (@lem362642 A B R S' a b P p1)). Qed.
Lemma lem362645 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term172 A B R S' a b P) = (term173 A B R S' a b P).
Proof. exact (fun_ext (fun p1 : A => @lem362644 A B R S' a b P p1)). Qed.
Lemma lem362646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362647 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term159 A B R S' a b P) = (term174 A B R S' a b P).
Proof. exact (MK_COMB (@lem362646 A) (@lem362645 A B R S' a b P)). Qed.
Lemma lem362648 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : ((term158 A B R S' a b P) = (term159 A B R S' a b P)) = ((term155 A B R S' a b P) = (term174 A B R S' a b P)).
Proof. exact (MK_COMB (@lem362640 A B R S' a b P) (@lem362647 A B R S' a b P)). Qed.
Lemma lem362649 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term155 A B R S' a b P) = (term174 A B R S' a b P).
Proof. exact (EQ_MP (@lem362648 A B R S' a b P) (@lem362634 A B R S' a b P)). Qed.
Lemma lem362664 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term175 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem362665 {A B : Type'} (r1 : A) (s1 : B) : r1 = (term175 A B r1 s1).
Proof. exact (@lem362664 A B r1 s1). Qed.
Lemma lem362666 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term176 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem362667 {A B : Type'} (r1 : A) (s1 : B) : s1 = (term176 A B r1 s1).
Proof. exact (@lem362666 A B r1 s1). Qed.
Lemma lem362668 {A : Type'} (r1 : A) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem362669 {A : Type'} : (term177 A) = (term177 A).
Proof. exact (eq_refl (term177 A)). Qed.
Lemma lem362670 {A B : Type'} (r1 : A) (s1 : B) : (term178 A r1) = (term179 A B r1 s1).
Proof. exact (MK_COMB (@lem362669 A) (@lem362665 A B r1 s1)). Qed.
Lemma lem362671 {A B : Type'} (r1 : A) (s1 : B) : (term179 A B r1 s1) = (term175 A B r1 s1).
Proof. exact (eq_refl (term179 A B r1 s1)). Qed.
Lemma lem362672 {A : Type'} (r1 : A) : (term180 A r1) = (term180 A r1).
Proof. exact (eq_refl (term180 A r1)). Qed.
Lemma lem362673 {A B : Type'} (r1 : A) (s1 : B) : ((term178 A r1) = (term179 A B r1 s1)) = ((term178 A r1) = (term175 A B r1 s1)).
Proof. exact (MK_COMB (@lem362672 A r1) (@lem362671 A B r1 s1)). Qed.
Lemma lem362674 {A : Type'} (r1 : A) : (term178 A r1) = r1.
Proof. exact (eq_refl (term178 A r1)). Qed.
Lemma lem362675 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem362676 {A : Type'} (r1 : A) : (term180 A r1) = (@eq A r1).
Proof. exact (MK_COMB (@lem362675 A) (@lem362674 A r1)). Qed.
Lemma lem362677 {A B : Type'} (r1 : A) (s1 : B) : (term175 A B r1 s1) = (term175 A B r1 s1).
Proof. exact (eq_refl (term175 A B r1 s1)). Qed.
Lemma lem362678 {A B : Type'} (r1 : A) (s1 : B) : ((term178 A r1) = (term175 A B r1 s1)) = (r1 = (term175 A B r1 s1)).
Proof. exact (MK_COMB (@lem362676 A r1) (@lem362677 A B r1 s1)). Qed.
Lemma lem362679 {A B : Type'} (r1 : A) (s1 : B) : ((term178 A r1) = (term179 A B r1 s1)) = (r1 = (term175 A B r1 s1)).
Proof. exact (TRANS (@lem362673 A B r1 s1) (@lem362678 A B r1 s1)). Qed.
Lemma lem362680 {A B : Type'} (r1 : A) (s1 : B) : r1 = (term175 A B r1 s1).
Proof. exact (EQ_MP (@lem362679 A B r1 s1) (@lem362670 A B r1 s1)). Qed.
Lemma lem362681 {A : Type'} (r1 : A) : (@eq A r1) = (@eq A r1).
Proof. exact (eq_refl (@eq A r1)). Qed.
Lemma lem362682 {A B : Type'} (r1 : A) (s1 : B) : (r1 = r1) = (r1 = (term175 A B r1 s1)).
Proof. exact (MK_COMB (@lem362681 A r1) (@lem362680 A B r1 s1)). Qed.
Lemma lem362683 {A B : Type'} (r1 : A) (s1 : B) : r1 = (term175 A B r1 s1).
Proof. exact (EQ_MP (@lem362682 A B r1 s1) (@lem362668 A r1)). Qed.
Lemma lem362684 {B : Type'} (s1 : B) : s1 = s1.
Proof. exact (eq_refl s1). Qed.
Lemma lem362685 {B : Type'} : (term177 B) = (term177 B).
Proof. exact (eq_refl (term177 B)). Qed.
Lemma lem362686 {A B : Type'} (r1 : A) (s1 : B) : (term178 B s1) = (term181 A B r1 s1).
Proof. exact (MK_COMB (@lem362685 B) (@lem362667 A B r1 s1)). Qed.
Lemma lem362687 {A B : Type'} (r1 : A) (s1 : B) : (term181 A B r1 s1) = (term176 A B r1 s1).
Proof. exact (eq_refl (term181 A B r1 s1)). Qed.
Lemma lem362688 {B : Type'} (s1 : B) : (term180 B s1) = (term180 B s1).
Proof. exact (eq_refl (term180 B s1)). Qed.
Lemma lem362689 {A B : Type'} (r1 : A) (s1 : B) : ((term178 B s1) = (term181 A B r1 s1)) = ((term178 B s1) = (term176 A B r1 s1)).
Proof. exact (MK_COMB (@lem362688 B s1) (@lem362687 A B r1 s1)). Qed.
Lemma lem362690 {B : Type'} (s1 : B) : (term178 B s1) = s1.
Proof. exact (eq_refl (term178 B s1)). Qed.
Lemma lem362691 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem362692 {B : Type'} (s1 : B) : (term180 B s1) = (@eq B s1).
Proof. exact (MK_COMB (@lem362691 B) (@lem362690 B s1)). Qed.
Lemma lem362693 {A B : Type'} (r1 : A) (s1 : B) : (term176 A B r1 s1) = (term176 A B r1 s1).
Proof. exact (eq_refl (term176 A B r1 s1)). Qed.
Lemma lem362694 {A B : Type'} (r1 : A) (s1 : B) : ((term178 B s1) = (term176 A B r1 s1)) = (s1 = (term176 A B r1 s1)).
Proof. exact (MK_COMB (@lem362692 B s1) (@lem362693 A B r1 s1)). Qed.
Lemma lem362695 {A B : Type'} (r1 : A) (s1 : B) : ((term178 B s1) = (term181 A B r1 s1)) = (s1 = (term176 A B r1 s1)).
Proof. exact (TRANS (@lem362689 A B r1 s1) (@lem362694 A B r1 s1)). Qed.
Lemma lem362696 {A B : Type'} (r1 : A) (s1 : B) : s1 = (term176 A B r1 s1).
Proof. exact (EQ_MP (@lem362695 A B r1 s1) (@lem362686 A B r1 s1)). Qed.
Lemma lem362697 {B : Type'} (s1 : B) : (@eq B s1) = (@eq B s1).
Proof. exact (eq_refl (@eq B s1)). Qed.
Lemma lem362698 {A B : Type'} (r1 : A) (s1 : B) : (s1 = s1) = (s1 = (term176 A B r1 s1)).
Proof. exact (MK_COMB (@lem362697 B s1) (@lem362696 A B r1 s1)). Qed.
Lemma lem362699 {A B : Type'} (r1 : A) (s1 : B) : s1 = (term176 A B r1 s1).
Proof. exact (EQ_MP (@lem362698 A B r1 s1) (@lem362684 B s1)). Qed.
Lemma lem362700 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term182 A B R S') = (term182 A B R S').
Proof. exact (eq_refl (term182 A B R S')). Qed.
Lemma lem362701 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term183 A B R S' r1) = (term184 A B R S' r1 s1).
Proof. exact (MK_COMB (@lem362700 A B R S') (@lem362683 A B r1 s1)). Qed.
Lemma lem362702 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term184 A B R S' r1 s1) = (term185 A B R S' r1 s1).
Proof. exact (eq_refl (term184 A B R S' r1 s1)). Qed.
Lemma lem362703 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term186 A B R S' r1) = (term186 A B R S' r1).
Proof. exact (eq_refl (term186 A B R S' r1)). Qed.
Lemma lem362704 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term183 A B R S' r1) = (term184 A B R S' r1 s1)) = ((term183 A B R S' r1) = (term185 A B R S' r1 s1)).
Proof. exact (MK_COMB (@lem362703 A B R S' r1) (@lem362702 A B R S' r1 s1)). Qed.
Lemma lem362705 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term183 A B R S' r1) = (term187 A B R S' r1).
Proof. exact (eq_refl (term183 A B R S' r1)). Qed.
Lemma lem362706 {A B : Type'} : (@eq (B -> (prod A B) -> Prop)) = (@eq (B -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@eq (B -> (prod A B) -> Prop))). Qed.
Lemma lem362707 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term186 A B R S' r1) = (term188 A B R S' r1).
Proof. exact (MK_COMB (@lem362706 A B) (@lem362705 A B R S' r1)). Qed.
Lemma lem362708 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term185 A B R S' r1 s1) = (term185 A B R S' r1 s1).
Proof. exact (eq_refl (term185 A B R S' r1 s1)). Qed.
Lemma lem362709 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term183 A B R S' r1) = (term185 A B R S' r1 s1)) = ((term187 A B R S' r1) = (term185 A B R S' r1 s1)).
Proof. exact (MK_COMB (@lem362707 A B R S' r1) (@lem362708 A B R S' r1 s1)). Qed.
Lemma lem362710 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term183 A B R S' r1) = (term184 A B R S' r1 s1)) = ((term187 A B R S' r1) = (term185 A B R S' r1 s1)).
Proof. exact (TRANS (@lem362704 A B R S' r1 s1) (@lem362709 A B R S' r1 s1)). Qed.
Lemma lem362711 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term187 A B R S' r1) = (term185 A B R S' r1 s1).
Proof. exact (EQ_MP (@lem362710 A B R S' r1 s1) (@lem362701 A B R S' r1 s1)). Qed.
Lemma lem362712 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term189 A B R S' r1 s1) = (term190 A B R S' r1 s1).
Proof. exact (MK_COMB (@lem362711 A B R S' r1 s1) (@lem362699 A B r1 s1)). Qed.
Lemma lem362713 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term190 A B R S' r1 s1) = (term191 A B R S' r1 s1).
Proof. exact (eq_refl (term190 A B R S' r1 s1)). Qed.
Lemma lem362714 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term192 A B R S' r1 s1) = (term192 A B R S' r1 s1).
Proof. exact (eq_refl (term192 A B R S' r1 s1)). Qed.
Lemma lem362715 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term189 A B R S' r1 s1) = (term190 A B R S' r1 s1)) = ((term189 A B R S' r1 s1) = (term191 A B R S' r1 s1)).
Proof. exact (MK_COMB (@lem362714 A B R S' r1 s1) (@lem362713 A B R S' r1 s1)). Qed.
Lemma lem362716 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term189 A B R S' r1 s1) = (term193 A B R S' r1 s1).
Proof. exact (eq_refl (term189 A B R S' r1 s1)). Qed.
Lemma lem362717 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem362718 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term192 A B R S' r1 s1) = (term194 A B R S' r1 s1).
Proof. exact (MK_COMB (@lem362717 A B) (@lem362716 A B R S' r1 s1)). Qed.
Lemma lem362719 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term191 A B R S' r1 s1) = (term191 A B R S' r1 s1).
Proof. exact (eq_refl (term191 A B R S' r1 s1)). Qed.
Lemma lem362720 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term189 A B R S' r1 s1) = (term191 A B R S' r1 s1)) = ((term193 A B R S' r1 s1) = (term191 A B R S' r1 s1)).
Proof. exact (MK_COMB (@lem362718 A B R S' r1 s1) (@lem362719 A B R S' r1 s1)). Qed.
Lemma lem362721 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term189 A B R S' r1 s1) = (term190 A B R S' r1 s1)) = ((term193 A B R S' r1 s1) = (term191 A B R S' r1 s1)).
Proof. exact (TRANS (@lem362715 A B R S' r1 s1) (@lem362720 A B R S' r1 s1)). Qed.
Lemma lem362722 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term193 A B R S' r1 s1) = (term191 A B R S' r1 s1).
Proof. exact (EQ_MP (@lem362721 A B R S' r1 s1) (@lem362712 A B R S' r1 s1)). Qed.
Lemma lem362723 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term191 A B R S' r1 s1) = (term193 A B R S' r1 s1).
Proof. exact (SYM (@lem362722 A B R S' r1 s1)). Qed.
Lemma lem362724 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term195 A B R S' r1 s1) = (term191 A B R S' r1 s1).
Proof. exact (eq_refl (term195 A B R S' r1 s1)). Qed.
Lemma lem362725 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term195 A B R S' r1 s1) = (term193 A B R S' r1 s1).
Proof. exact (TRANS (@lem362724 A B R S' r1 s1) (@lem362723 A B R S' r1 s1)). Qed.
Lemma lem362726 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : term196 A B R S' r1.
Proof. exact (fun s1 : B => @lem362725 A B R S' r1 s1). Qed.
Lemma lem362727 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term197 A B R S'.
Proof. exact (fun r1 : A => @lem362726 A B R S' r1). Qed.
Lemma lem362728 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term198 A B R S'.
Proof. exact (ex_intro (term199 A B R S') (term200 A B R S') (@lem362727 A B R S')). Qed.
Lemma lem362730 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem362731 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (a = b) = (@GEQ ((prod A B) -> Prop) a b).
Proof. exact (@lem362730 (type1210 A B) a b). Qed.
Lemma lem362732 {A B : Type'} (_7843 : type1204 A B) (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : ((term201 A B _7843 r1 s1) = (term193 A B R S' r1 s1)) = (term202 A B _7843 R S' r1 s1).
Proof. exact (@lem362731 A B (term201 A B _7843 r1 s1) (term193 A B R S' r1 s1)). Qed.
Lemma lem362733 {A B : Type'} (_7843 : type1204 A B) (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term203 A B _7843 R S' r1) = (term204 A B _7843 R S' r1).
Proof. exact (fun_ext (fun s1 : B => @lem362732 A B _7843 R S' r1 s1)). Qed.
Lemma lem362734 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362735 {A B : Type'} (_7843 : type1204 A B) (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term205 A B _7843 R S' r1) = (term206 A B _7843 R S' r1).
Proof. exact (MK_COMB (@lem362734 B) (@lem362733 A B _7843 R S' r1)). Qed.
Lemma lem362736 {A B : Type'} (_7843 : type1204 A B) (R : type1402 A) (S' : type1406 A B) : (term207 A B _7843 R S') = (term208 A B _7843 R S').
Proof. exact (fun_ext (fun r1 : A => @lem362735 A B _7843 R S' r1)). Qed.
Lemma lem362737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362738 {A B : Type'} (_7843 : type1204 A B) (R : type1402 A) (S' : type1406 A B) : (term209 A B _7843 R S') = (term210 A B _7843 R S').
Proof. exact (MK_COMB (@lem362737 A) (@lem362736 A B _7843 R S')). Qed.
Lemma lem362739 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term199 A B R S') = (term211 A B R S').
Proof. exact (fun_ext (fun _7843 : type1204 A B => @lem362738 A B _7843 R S')). Qed.
Lemma lem362740 {A B : Type'} : (@ex ((prod A B) -> (prod A B) -> Prop)) = (@ex ((prod A B) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> (prod A B) -> Prop))). Qed.
Lemma lem362741 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term198 A B R S') = (term212 A B R S').
Proof. exact (MK_COMB (@lem362740 A B) (@lem362739 A B R S')). Qed.
Lemma lem362742 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term212 A B R S'.
Proof. exact (EQ_MP (@lem362741 A B R S') (@lem362728 A B R S')). Qed.
Lemma lem362744 {_5076 : Type'} (P : _5076 -> Prop) : term213 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem362745 {A B : Type'} (P : type315 A B) : term214 A B P.
Proof. exact (@lem362744 (type1204 A B) P). Qed.
Lemma lem362746 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term215 A B R S'.
Proof. exact (@lem362745 A B (term211 A B R S')). Qed.
Lemma lem362747 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term216 A B R S'.
Proof. exact (@lem362746 A B R S' (@lem362742 A B R S')). Qed.
Lemma lem362748 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : (term216 A B R S') = (term217 A B R S').
Proof. exact (eq_refl (term216 A B R S')). Qed.
Lemma lem362749 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term217 A B R S'.
Proof. exact (EQ_MP (@lem362748 A B R S') (@lem362747 A B R S')). Qed.
Lemma lem362750 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : term218 A B R S' r1.
Proof. exact (@lem362749 A B R S' r1). Qed.
Lemma lem362751 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : (term218 A B R S' r1) = (term219 A B R S' r1).
Proof. exact (eq_refl (term218 A B R S' r1)). Qed.
Lemma lem362752 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) : term219 A B R S' r1.
Proof. exact (EQ_MP (@lem362751 A B R S' r1) (@lem362750 A B R S' r1)). Qed.
Lemma lem362753 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : term220 A B R S' r1 s1.
Proof. exact (@lem362752 A B R S' r1 s1). Qed.
Lemma lem362754 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term220 A B R S' r1 s1) = (term221 A B R S' r1 s1).
Proof. exact (eq_refl (term220 A B R S' r1 s1)). Qed.
Lemma lem362755 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : term221 A B R S' r1 s1.
Proof. exact (EQ_MP (@lem362754 A B R S' r1 s1) (@lem362753 A B R S' r1 s1)). Qed.
Lemma lem362757 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem362758 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (@GEQ ((prod A B) -> Prop) a b) = (a = b).
Proof. exact (@lem362757 (type1210 A B) a b). Qed.
Lemma lem362759 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term221 A B R S' r1 s1) = ((term222 A B R S' r1 s1) = (term193 A B R S' r1 s1)).
Proof. exact (@lem362758 A B (term222 A B R S' r1 s1) (term193 A B R S' r1 s1)). Qed.
Lemma lem362760 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term222 A B R S' r1 s1) = (term193 A B R S' r1 s1).
Proof. exact (EQ_MP (@lem362759 A B R S' r1 s1) (@lem362755 A B R S' r1 s1)). Qed.
Lemma lem362761 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (r1 : A) (s1 : B) : (term222 A B R S' r1 s1) = (term193 A B R S' r1 s1).
Proof. exact (@lem362760 A B R S' r1 s1). Qed.
Lemma lem362762 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term222 A B R S' p1 p2) = (term193 A B R S' p1 p2).
Proof. exact (@lem362761 A B R S' p1 p2). Qed.
Lemma lem362781 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@pair A B a b).
Proof. exact (eq_refl (@pair A B a b)). Qed.
Lemma lem362782 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (a : A) (b : B) : (term223 A B R S' p1 p2 a b) = (term224 A B R S' p1 p2 a b).
Proof. exact (MK_COMB (@lem362762 A B R S' p1 p2) (@lem362781 A B a b)). Qed.
Lemma lem362783 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term175 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem362784 {A B : Type'} (r2 : A) (s2 : B) : r2 = (term175 A B r2 s2).
Proof. exact (@lem362783 A B r2 s2). Qed.
Lemma lem362785 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term176 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem362786 {A B : Type'} (r2 : A) (s2 : B) : s2 = (term176 A B r2 s2).
Proof. exact (@lem362785 A B r2 s2). Qed.
Lemma lem362787 {A : Type'} (r2 : A) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem362788 {A : Type'} : (term177 A) = (term177 A).
Proof. exact (eq_refl (term177 A)). Qed.
Lemma lem362789 {A B : Type'} (r2 : A) (s2 : B) : (term178 A r2) = (term179 A B r2 s2).
Proof. exact (MK_COMB (@lem362788 A) (@lem362784 A B r2 s2)). Qed.
Lemma lem362790 {A B : Type'} (r2 : A) (s2 : B) : (term179 A B r2 s2) = (term175 A B r2 s2).
Proof. exact (eq_refl (term179 A B r2 s2)). Qed.
Lemma lem362791 {A : Type'} (r2 : A) : (term180 A r2) = (term180 A r2).
Proof. exact (eq_refl (term180 A r2)). Qed.
Lemma lem362792 {A B : Type'} (r2 : A) (s2 : B) : ((term178 A r2) = (term179 A B r2 s2)) = ((term178 A r2) = (term175 A B r2 s2)).
Proof. exact (MK_COMB (@lem362791 A r2) (@lem362790 A B r2 s2)). Qed.
Lemma lem362793 {A : Type'} (r2 : A) : (term178 A r2) = r2.
Proof. exact (eq_refl (term178 A r2)). Qed.
Lemma lem362794 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem362795 {A : Type'} (r2 : A) : (term180 A r2) = (@eq A r2).
Proof. exact (MK_COMB (@lem362794 A) (@lem362793 A r2)). Qed.
Lemma lem362796 {A B : Type'} (r2 : A) (s2 : B) : (term175 A B r2 s2) = (term175 A B r2 s2).
Proof. exact (eq_refl (term175 A B r2 s2)). Qed.
Lemma lem362797 {A B : Type'} (r2 : A) (s2 : B) : ((term178 A r2) = (term175 A B r2 s2)) = (r2 = (term175 A B r2 s2)).
Proof. exact (MK_COMB (@lem362795 A r2) (@lem362796 A B r2 s2)). Qed.
Lemma lem362798 {A B : Type'} (r2 : A) (s2 : B) : ((term178 A r2) = (term179 A B r2 s2)) = (r2 = (term175 A B r2 s2)).
Proof. exact (TRANS (@lem362792 A B r2 s2) (@lem362797 A B r2 s2)). Qed.
Lemma lem362799 {A B : Type'} (r2 : A) (s2 : B) : r2 = (term175 A B r2 s2).
Proof. exact (EQ_MP (@lem362798 A B r2 s2) (@lem362789 A B r2 s2)). Qed.
Lemma lem362800 {A : Type'} (r2 : A) : (@eq A r2) = (@eq A r2).
Proof. exact (eq_refl (@eq A r2)). Qed.
Lemma lem362801 {A B : Type'} (r2 : A) (s2 : B) : (r2 = r2) = (r2 = (term175 A B r2 s2)).
Proof. exact (MK_COMB (@lem362800 A r2) (@lem362799 A B r2 s2)). Qed.
Lemma lem362802 {A B : Type'} (r2 : A) (s2 : B) : r2 = (term175 A B r2 s2).
Proof. exact (EQ_MP (@lem362801 A B r2 s2) (@lem362787 A r2)). Qed.
Lemma lem362803 {B : Type'} (s2 : B) : s2 = s2.
Proof. exact (eq_refl s2). Qed.
Lemma lem362804 {B : Type'} : (term177 B) = (term177 B).
Proof. exact (eq_refl (term177 B)). Qed.
Lemma lem362805 {A B : Type'} (r2 : A) (s2 : B) : (term178 B s2) = (term181 A B r2 s2).
Proof. exact (MK_COMB (@lem362804 B) (@lem362786 A B r2 s2)). Qed.
Lemma lem362806 {A B : Type'} (r2 : A) (s2 : B) : (term181 A B r2 s2) = (term176 A B r2 s2).
Proof. exact (eq_refl (term181 A B r2 s2)). Qed.
Lemma lem362807 {B : Type'} (s2 : B) : (term180 B s2) = (term180 B s2).
Proof. exact (eq_refl (term180 B s2)). Qed.
Lemma lem362808 {A B : Type'} (r2 : A) (s2 : B) : ((term178 B s2) = (term181 A B r2 s2)) = ((term178 B s2) = (term176 A B r2 s2)).
Proof. exact (MK_COMB (@lem362807 B s2) (@lem362806 A B r2 s2)). Qed.
Lemma lem362809 {B : Type'} (s2 : B) : (term178 B s2) = s2.
Proof. exact (eq_refl (term178 B s2)). Qed.
Lemma lem362810 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem362811 {B : Type'} (s2 : B) : (term180 B s2) = (@eq B s2).
Proof. exact (MK_COMB (@lem362810 B) (@lem362809 B s2)). Qed.
Lemma lem362812 {A B : Type'} (r2 : A) (s2 : B) : (term176 A B r2 s2) = (term176 A B r2 s2).
Proof. exact (eq_refl (term176 A B r2 s2)). Qed.
Lemma lem362813 {A B : Type'} (r2 : A) (s2 : B) : ((term178 B s2) = (term176 A B r2 s2)) = (s2 = (term176 A B r2 s2)).
Proof. exact (MK_COMB (@lem362811 B s2) (@lem362812 A B r2 s2)). Qed.
Lemma lem362814 {A B : Type'} (r2 : A) (s2 : B) : ((term178 B s2) = (term181 A B r2 s2)) = (s2 = (term176 A B r2 s2)).
Proof. exact (TRANS (@lem362808 A B r2 s2) (@lem362813 A B r2 s2)). Qed.
Lemma lem362815 {A B : Type'} (r2 : A) (s2 : B) : s2 = (term176 A B r2 s2).
Proof. exact (EQ_MP (@lem362814 A B r2 s2) (@lem362805 A B r2 s2)). Qed.
Lemma lem362816 {B : Type'} (s2 : B) : (@eq B s2) = (@eq B s2).
Proof. exact (eq_refl (@eq B s2)). Qed.
Lemma lem362817 {A B : Type'} (r2 : A) (s2 : B) : (s2 = s2) = (s2 = (term176 A B r2 s2)).
Proof. exact (MK_COMB (@lem362816 B s2) (@lem362815 A B r2 s2)). Qed.
Lemma lem362818 {A B : Type'} (r2 : A) (s2 : B) : s2 = (term176 A B r2 s2).
Proof. exact (EQ_MP (@lem362817 A B r2 s2) (@lem362803 B s2)). Qed.
Lemma lem362819 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term225 A B R S' p1 p2) = (term225 A B R S' p1 p2).
Proof. exact (eq_refl (term225 A B R S' p1 p2)). Qed.
Lemma lem362820 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term226 A B R S' p1 p2 r2) = (term227 A B R S' p1 p2 r2 s2).
Proof. exact (MK_COMB (@lem362819 A B R S' p1 p2) (@lem362802 A B r2 s2)). Qed.
Lemma lem362821 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : (term227 A B R S' p1 p2 r2 s2) = (term228 A B R r2 s2 S' p1 p2).
Proof. exact (eq_refl (term227 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362822 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) : (term229 A B R S' p1 p2 r2) = (term229 A B R S' p1 p2 r2).
Proof. exact (eq_refl (term229 A B R S' p1 p2 r2)). Qed.
Lemma lem362823 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : ((term226 A B R S' p1 p2 r2) = (term227 A B R S' p1 p2 r2 s2)) = ((term226 A B R S' p1 p2 r2) = (term228 A B R r2 s2 S' p1 p2)).
Proof. exact (MK_COMB (@lem362822 A B R S' p1 p2 r2) (@lem362821 A B R r2 s2 S' p1 p2)). Qed.
Lemma lem362824 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term226 A B R S' p1 p2 r2) = (term230 A B R r2 S' p1 p2).
Proof. exact (eq_refl (term226 A B R S' p1 p2 r2)). Qed.
Lemma lem362825 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem362826 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term229 A B R S' p1 p2 r2) = (term231 A B R r2 S' p1 p2).
Proof. exact (MK_COMB (@lem362825 B) (@lem362824 A B R r2 S' p1 p2)). Qed.
Lemma lem362827 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : (term228 A B R r2 s2 S' p1 p2) = (term228 A B R r2 s2 S' p1 p2).
Proof. exact (eq_refl (term228 A B R r2 s2 S' p1 p2)). Qed.
Lemma lem362828 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : ((term226 A B R S' p1 p2 r2) = (term228 A B R r2 s2 S' p1 p2)) = ((term230 A B R r2 S' p1 p2) = (term228 A B R r2 s2 S' p1 p2)).
Proof. exact (MK_COMB (@lem362826 A B R r2 S' p1 p2) (@lem362827 A B R r2 s2 S' p1 p2)). Qed.
Lemma lem362829 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : ((term226 A B R S' p1 p2 r2) = (term227 A B R S' p1 p2 r2 s2)) = ((term230 A B R r2 S' p1 p2) = (term228 A B R r2 s2 S' p1 p2)).
Proof. exact (TRANS (@lem362823 A B R r2 s2 S' p1 p2) (@lem362828 A B R r2 s2 S' p1 p2)). Qed.
Lemma lem362830 {A B : Type'} (R : type1402 A) (r2 : A) (s2 : B) (S' : type1406 A B) (p1 : A) (p2 : B) : (term230 A B R r2 S' p1 p2) = (term228 A B R r2 s2 S' p1 p2).
Proof. exact (EQ_MP (@lem362829 A B R r2 s2 S' p1 p2) (@lem362820 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362831 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term232 A B R r2 S' p1 p2 s2) = (term233 A B R S' p1 p2 r2 s2).
Proof. exact (MK_COMB (@lem362830 A B R r2 s2 S' p1 p2) (@lem362818 A B r2 s2)). Qed.
Lemma lem362832 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term233 A B R S' p1 p2 r2 s2) = (term234 A B R S' p1 p2 r2 s2).
Proof. exact (eq_refl (term233 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362833 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term235 A B R r2 S' p1 p2 s2) = (term235 A B R r2 S' p1 p2 s2).
Proof. exact (eq_refl (term235 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362834 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : ((term232 A B R r2 S' p1 p2 s2) = (term233 A B R S' p1 p2 r2 s2)) = ((term232 A B R r2 S' p1 p2 s2) = (term234 A B R S' p1 p2 r2 s2)).
Proof. exact (MK_COMB (@lem362833 A B R r2 S' p1 p2 s2) (@lem362832 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362835 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term232 A B R r2 S' p1 p2 s2) = (term236 A B R r2 S' p1 p2 s2).
Proof. exact (eq_refl (term232 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem362837 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term235 A B R r2 S' p1 p2 s2) = (term237 A B R r2 S' p1 p2 s2).
Proof. exact (MK_COMB (@lem362836) (@lem362835 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362838 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term234 A B R S' p1 p2 r2 s2) = (term234 A B R S' p1 p2 r2 s2).
Proof. exact (eq_refl (term234 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362839 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : ((term232 A B R r2 S' p1 p2 s2) = (term234 A B R S' p1 p2 r2 s2)) = ((term236 A B R r2 S' p1 p2 s2) = (term234 A B R S' p1 p2 r2 s2)).
Proof. exact (MK_COMB (@lem362837 A B R r2 S' p1 p2 s2) (@lem362838 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362840 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : ((term232 A B R r2 S' p1 p2 s2) = (term233 A B R S' p1 p2 r2 s2)) = ((term236 A B R r2 S' p1 p2 s2) = (term234 A B R S' p1 p2 r2 s2)).
Proof. exact (TRANS (@lem362834 A B R S' p1 p2 r2 s2) (@lem362839 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362841 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term236 A B R r2 S' p1 p2 s2) = (term234 A B R S' p1 p2 r2 s2).
Proof. exact (EQ_MP (@lem362840 A B R S' p1 p2 r2 s2) (@lem362831 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362842 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term234 A B R S' p1 p2 r2 s2) = (term236 A B R r2 S' p1 p2 s2).
Proof. exact (SYM (@lem362841 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362843 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) (s2 : B) : (term238 A B R S' p1 p2 r2 s2) = (term234 A B R S' p1 p2 r2 s2).
Proof. exact (eq_refl (term238 A B R S' p1 p2 r2 s2)). Qed.
Lemma lem362844 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term238 A B R S' p1 p2 r2 s2) = (term236 A B R r2 S' p1 p2 s2).
Proof. exact (TRANS (@lem362843 A B R S' p1 p2 r2 s2) (@lem362842 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362845 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : term239 A B R r2 S' p1 p2.
Proof. exact (fun s2 : B => @lem362844 A B R r2 S' p1 p2 s2). Qed.
Lemma lem362846 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term240 A B R S' p1 p2.
Proof. exact (fun r2 : A => @lem362845 A B R r2 S' p1 p2). Qed.
Lemma lem362847 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term241 A B R S' p1 p2.
Proof. exact (ex_intro (term242 A B R S' p1 p2) (term243 A B R S' p1 p2) (@lem362846 A B R S' p1 p2)). Qed.
Lemma lem362849 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem362850 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem362849 Prop a b). Qed.
Lemma lem362851 {A B : Type'} (_7855 : type1210 A B) (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : ((term52 A B _7855 r2 s2) = (term236 A B R r2 S' p1 p2 s2)) = (term244 A B _7855 R r2 S' p1 p2 s2).
Proof. exact (@lem362850 (term52 A B _7855 r2 s2) (term236 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362852 {A B : Type'} (_7855 : type1210 A B) (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term245 A B _7855 R r2 S' p1 p2) = (term246 A B _7855 R r2 S' p1 p2).
Proof. exact (fun_ext (fun s2 : B => @lem362851 A B _7855 R r2 S' p1 p2 s2)). Qed.
Lemma lem362853 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362854 {A B : Type'} (_7855 : type1210 A B) (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term247 A B _7855 R r2 S' p1 p2) = (term248 A B _7855 R r2 S' p1 p2).
Proof. exact (MK_COMB (@lem362853 B) (@lem362852 A B _7855 R r2 S' p1 p2)). Qed.
Lemma lem362855 {A B : Type'} (_7855 : type1210 A B) (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term249 A B _7855 R S' p1 p2) = (term250 A B _7855 R S' p1 p2).
Proof. exact (fun_ext (fun r2 : A => @lem362854 A B _7855 R r2 S' p1 p2)). Qed.
Lemma lem362856 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362857 {A B : Type'} (_7855 : type1210 A B) (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term251 A B _7855 R S' p1 p2) = (term252 A B _7855 R S' p1 p2).
Proof. exact (MK_COMB (@lem362856 A) (@lem362855 A B _7855 R S' p1 p2)). Qed.
Lemma lem362858 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term242 A B R S' p1 p2) = (term253 A B R S' p1 p2).
Proof. exact (fun_ext (fun _7855 : type1210 A B => @lem362857 A B _7855 R S' p1 p2)). Qed.
Lemma lem362859 {A B : Type'} : (@ex ((prod A B) -> Prop)) = (@ex ((prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> Prop))). Qed.
Lemma lem362860 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term241 A B R S' p1 p2) = (term254 A B R S' p1 p2).
Proof. exact (MK_COMB (@lem362859 A B) (@lem362858 A B R S' p1 p2)). Qed.
Lemma lem362861 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term254 A B R S' p1 p2.
Proof. exact (EQ_MP (@lem362860 A B R S' p1 p2) (@lem362847 A B R S' p1 p2)). Qed.
Lemma lem362863 {_5076 : Type'} (P : _5076 -> Prop) : term213 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem362864 {A B : Type'} (P : type324 A B) : term255 A B P.
Proof. exact (@lem362863 (type1210 A B) P). Qed.
Lemma lem362865 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term256 A B R S' p1 p2.
Proof. exact (@lem362864 A B (term253 A B R S' p1 p2)). Qed.
Lemma lem362866 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term257 A B R S' p1 p2.
Proof. exact (@lem362865 A B R S' p1 p2 (@lem362861 A B R S' p1 p2)). Qed.
Lemma lem362867 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term257 A B R S' p1 p2) = (term258 A B R S' p1 p2).
Proof. exact (eq_refl (term257 A B R S' p1 p2)). Qed.
Lemma lem362868 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) : term258 A B R S' p1 p2.
Proof. exact (EQ_MP (@lem362867 A B R S' p1 p2) (@lem362866 A B R S' p1 p2)). Qed.
Lemma lem362869 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (p1 : A) (p2 : B) (r2 : A) : term259 A B R S' p1 p2 r2.
Proof. exact (@lem362868 A B R S' p1 p2 r2). Qed.
Lemma lem362870 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : (term259 A B R S' p1 p2 r2) = (term260 A B R r2 S' p1 p2).
Proof. exact (eq_refl (term259 A B R S' p1 p2 r2)). Qed.
Lemma lem362871 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) : term260 A B R r2 S' p1 p2.
Proof. exact (EQ_MP (@lem362870 A B R r2 S' p1 p2) (@lem362869 A B R S' p1 p2 r2)). Qed.
Lemma lem362872 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : term261 A B R r2 S' p1 p2 s2.
Proof. exact (@lem362871 A B R r2 S' p1 p2 s2). Qed.
Lemma lem362873 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term261 A B R r2 S' p1 p2 s2) = (term262 A B R r2 S' p1 p2 s2).
Proof. exact (eq_refl (term261 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362874 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : term262 A B R r2 S' p1 p2 s2.
Proof. exact (EQ_MP (@lem362873 A B R r2 S' p1 p2 s2) (@lem362872 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362876 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem362877 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem362876 Prop a b). Qed.
Lemma lem362878 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term262 A B R r2 S' p1 p2 s2) = ((term224 A B R S' p1 p2 r2 s2) = (term236 A B R r2 S' p1 p2 s2)).
Proof. exact (@lem362877 (term224 A B R S' p1 p2 r2 s2) (term236 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362879 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term224 A B R S' p1 p2 r2 s2) = (term236 A B R r2 S' p1 p2 s2).
Proof. exact (EQ_MP (@lem362878 A B R r2 S' p1 p2 s2) (@lem362874 A B R r2 S' p1 p2 s2)). Qed.
Lemma lem362880 {A B : Type'} (R : type1402 A) (r2 : A) (S' : type1406 A B) (p1 : A) (p2 : B) (s2 : B) : (term224 A B R S' p1 p2 r2 s2) = (term236 A B R r2 S' p1 p2 s2).
Proof. exact (@lem362879 A B R r2 S' p1 p2 s2). Qed.
Lemma lem362881 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) : (term224 A B R S' p1 p2 a b) = (term236 A B R a S' p1 p2 b).
Proof. exact (@lem362880 A B R a S' p1 p2 b). Qed.
Lemma lem362888 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) : (term223 A B R S' p1 p2 a b) = (term236 A B R a S' p1 p2 b).
Proof. exact (TRANS (@lem362782 A B R S' p1 p2 a b) (@lem362881 A B R a S' p1 p2 b)). Qed.
Lemma lem362889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem362890 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) : (term263 A B R S' p1 p2 a b) = (term264 A B R a S' p1 p2 b).
Proof. exact (MK_COMB (@lem362889) (@lem362888 A B R a S' p1 p2 b)). Qed.
Lemma lem362891 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) : (term127 A B P p1 p2) = (term127 A B P p1 p2).
Proof. exact (eq_refl (term127 A B P p1 p2)). Qed.
Lemma lem362892 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) (p2 : B) : (term167 A B R S' a b P p1 p2) = (term265 A B R a S' b P p1 p2).
Proof. exact (MK_COMB (@lem362890 A B R a S' p1 p2 b) (@lem362891 A B P p1 p2)). Qed.
Lemma lem362895 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) : (term169 A B R S' a b P p1) = (term266 A B R a S' b P p1).
Proof. exact (fun_ext (fun p2 : B => @lem362892 A B R a S' b P p1 p2)). Qed.
Lemma lem362896 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem362897 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) : (term171 A B R S' a b P p1) = (term267 A B R a S' b P p1).
Proof. exact (MK_COMB (@lem362896 B) (@lem362895 A B R a S' b P p1)). Qed.
Lemma lem362904 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term173 A B R S' a b P) = (term268 A B R a S' b P).
Proof. exact (fun_ext (fun p1 : A => @lem362897 A B R a S' b P p1)). Qed.
Lemma lem362905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem362906 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term174 A B R S' a b P) = (term269 A B R a S' b P).
Proof. exact (MK_COMB (@lem362905 A) (@lem362904 A B R a S' b P)). Qed.
Lemma lem362913 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term155 A B R S' a b P) = (term269 A B R a S' b P).
Proof. exact (TRANS (@lem362649 A B R S' a b P) (@lem362906 A B R a S' b P)). Qed.
Lemma lem362914 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b : B) (P : type1210 A B) : (term269 A B R a S' b P) = (term155 A B R S' a b P).
Proof. exact (SYM (@lem362913 A B R a S' b P)). Qed.
Lemma lem362916 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem362917 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term269 A B R a S' b P) = (term271 A B R a S' b P).
Proof. exact (@lem362916 (term269 A B R a S' b P)). Qed.
Lemma lem362918 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term271 A B R a S' b P) = (term269 A B R a S' b P).
Proof. exact (SYM (@lem362917 A B R a S' b P)). Qed.
Lemma lem362919 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term272 A B R a S' b P) : term272 A B R a S' b P.
Proof. exact (h1). Qed.
Lemma lem362922 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term273 A B a0 b0 b1 R a S' b P) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (h1). Qed.
Lemma lem362923 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (fun h0 : term273 A B a0 b0 b1 R a S' b P => @lem362922 A B a0 b0 b1 R a S' b P h0). Qed.
Lemma lem362924 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term274 A B a0 b0 b1 R a S' b P) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (h1). Qed.
Lemma lem362925 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term273 A B a0 b0 b1 R a S' b P) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (h1). Qed.
Lemma lem362926 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term273 A B a0 b0 b1 R a S' b P) (h2 : term274 A B a0 b0 b1 R a S' b P) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (@lem362924 A B a0 b0 b1 R a S' b P h2 (@lem362925 A B a0 b0 b1 R a S' b P h1)). Qed.
Lemma lem362927 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term273 A B a0 b0 b1 R a S' b P) : term275 A B a0 b0 b1 R a S' b P.
Proof. exact (fun h0 : term274 A B a0 b0 b1 R a S' b P => @lem362926 A B a0 b0 b1 R a S' b P h1 h0). Qed.
Lemma lem362928 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term274 A B a0 b0 b1 R a S' b P) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (h1). Qed.
Lemma lem362929 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term273 A B a0 b0 b1 R a S' b P) (h2 : term274 A B a0 b0 b1 R a S' b P) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (@lem362927 A B a0 b0 b1 R a S' b P h1 (@lem362928 A B a0 b0 b1 R a S' b P h2)). Qed.
Lemma lem362930 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (h1 : term274 A B a0 b0 b1 R a S' b P) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (fun h0 : term273 A B a0 b0 b1 R a S' b P => @lem362929 A B a0 b0 b1 R a S' b P h0 h1). Qed.
Lemma lem362931 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term276 A B a0 b0 b1 R a S' b P.
Proof. exact (fun h0 : term274 A B a0 b0 b1 R a S' b P => @lem362930 A B a0 b0 b1 R a S' b P h0). Qed.
Lemma lem362934 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (@lem362931 A B a0 b0 b1 R a S' b P (@lem362923 A B a0 b0 b1 R a S' b P)). Qed.
Lemma lem362935 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term274 A B a0 b0 b1 R a S' b P.
Proof. exact (@lem362934 A B a0 b0 b1 R a S' b P). Qed.
Lemma lem362995 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem362996 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term271 A B R a S' b P) = (term277 A B R a S' b P).
Proof. exact (@lem362995 (term272 A B R a S' b P)). Qed.
Lemma lem362998 (t : Prop) : (term278 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem362999 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term277 A B R a S' b P) = (term269 A B R a S' b P).
Proof. exact (@lem362998 (term269 A B R a S' b P)). Qed.
Lemma lem363004 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term271 A B R a S' b P) = (term269 A B R a S' b P).
Proof. exact (TRANS (@lem362996 A B R a S' b P) (@lem362999 A B R a S' b P)). Qed.
Lemma lem363015 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term96 A B P a b) = (term96 A B P a b).
Proof. exact (eq_refl (term96 A B P a b)). Qed.
Lemma lem363016 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term279 A B R a S' b P) = (term280 A B R a S' b P).
Proof. exact (MK_COMB (@lem363015 A B P a b) (@lem363004 A B R a S' b P)). Qed.
Lemma lem363019 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term281 A B S' b P a) = (term281 A B S' b P a).
Proof. exact (eq_refl (term281 A B S' b P a)). Qed.
Lemma lem363020 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term282 A B R a S' b P) = (term283 A B R a S' b P).
Proof. exact (MK_COMB (@lem363019 A B S' b P a) (@lem363016 A B R a S' b P)). Qed.
Lemma lem363023 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) : (term96 A B P a b1) = (term96 A B P a b1).
Proof. exact (eq_refl (term96 A B P a b1)). Qed.
Lemma lem363024 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term284 A B b1 R a S' b P) = (term285 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363023 A B P a b1) (@lem363020 A B R a S' b P)). Qed.
Lemma lem363027 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term286 A B R a P) = (term286 A B R a P).
Proof. exact (eq_refl (term286 A B R a P)). Qed.
Lemma lem363028 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term287 A B b1 R a S' b P) = (term288 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363027 A B R a P) (@lem363024 A B b1 R a S' b P)). Qed.
Lemma lem363031 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) : (term96 A B P a0 b0) = (term96 A B P a0 b0).
Proof. exact (eq_refl (term96 A B P a0 b0)). Qed.
Lemma lem363032 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term273 A B a0 b0 b1 R a S' b P) = (term289 A B a0 b0 b1 R a S' b P).
Proof. exact (MK_COMB (@lem363031 A B P a0 b0) (@lem363028 A B b1 R a S' b P)). Qed.
Lemma lem363035 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term290 A B b0 b1 R a S' b P) = (term291 A B b0 b1 R a S' b P).
Proof. exact (fun_ext (fun a0 : A => @lem363032 A B a0 b0 b1 R a S' b P)). Qed.
Lemma lem363036 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363037 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term292 A B b0 b1 R a S' b P) = (term293 A B b0 b1 R a S' b P).
Proof. exact (MK_COMB (@lem363036 A) (@lem363035 A B b0 b1 R a S' b P)). Qed.
Lemma lem363042 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term294 A B b1 R a S' b P) = (term295 A B b1 R a S' b P).
Proof. exact (fun_ext (fun b0 : B => @lem363037 A B b0 b1 R a S' b P)). Qed.
Lemma lem363043 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363044 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term296 A B b1 R a S' b P) = (term297 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363043 B) (@lem363042 A B b1 R a S' b P)). Qed.
Lemma lem363049 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term298 A B R a S' b P) = (term299 A B R a S' b P).
Proof. exact (fun_ext (fun b1 : B => @lem363044 A B b1 R a S' b P)). Qed.
Lemma lem363050 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363051 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term300 A B R a S' b P) = (term301 A B R a S' b P).
Proof. exact (MK_COMB (@lem363050 B) (@lem363049 A B R a S' b P)). Qed.
Lemma lem363056 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term302 A B a S' b P) = (term303 A B a S' b P).
Proof. exact (fun_ext (fun R : type1402 A => @lem363051 A B R a S' b P)). Qed.
Lemma lem363057 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem363058 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term304 A B a S' b P) = (term305 A B a S' b P).
Proof. exact (MK_COMB (@lem363057 A) (@lem363056 A B a S' b P)). Qed.
Lemma lem363063 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : (term306 A B S' b P) = (term307 A B S' b P).
Proof. exact (fun_ext (fun a : A => @lem363058 A B a S' b P)). Qed.
Lemma lem363064 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363065 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : (term308 A B S' b P) = (term309 A B S' b P).
Proof. exact (MK_COMB (@lem363064 A) (@lem363063 A B S' b P)). Qed.
Lemma lem363070 {A B : Type'} (b : B) (P : type1210 A B) : (term310 A B b P) = (term311 A B b P).
Proof. exact (fun_ext (fun S' : type1406 A B => @lem363065 A B S' b P)). Qed.
Lemma lem363071 {A B : Type'} : (@all (A -> B -> B -> Prop)) = (@all (A -> B -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> B -> Prop))). Qed.
Lemma lem363072 {A B : Type'} (b : B) (P : type1210 A B) : (term312 A B b P) = (term313 A B b P).
Proof. exact (MK_COMB (@lem363071 A B) (@lem363070 A B b P)). Qed.
Lemma lem363077 {A B : Type'} (P : type1210 A B) : (term314 A B P) = (term315 A B P).
Proof. exact (fun_ext (fun b : B => @lem363072 A B b P)). Qed.
Lemma lem363078 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363079 {A B : Type'} (P : type1210 A B) : (term316 A B P) = (term317 A B P).
Proof. exact (MK_COMB (@lem363078 B) (@lem363077 A B P)). Qed.
Lemma lem363084 {A B : Type'} : (term318 A B) = (term319 A B).
Proof. exact (fun_ext (fun P : type1210 A B => @lem363079 A B P)). Qed.
Lemma lem363085 {A B : Type'} : (@all ((prod A B) -> Prop)) = (@all ((prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((prod A B) -> Prop))). Qed.
Lemma lem363094 {A B : Type'} : (term320 A B) = (term321 A B).
Proof. exact (MK_COMB (@lem363085 A B) (@lem363084 A B)). Qed.
Lemma lem363109 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) (p2 : B) : (term265 A B R a S' b P p1 p2) = (term265 A B R a S' b P p1 p2).
Proof. exact (eq_refl (term265 A B R a S' b P p1 p2)). Qed.
Lemma lem363110 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) : (term266 A B R a S' b P p1) = (term266 A B R a S' b P p1).
Proof. exact (fun_ext (fun p2 : B => @lem363109 A B R a S' b P p1 p2)). Qed.
Lemma lem363111 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363112 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (p1 : A) : (term267 A B R a S' b P p1) = (term267 A B R a S' b P p1).
Proof. exact (MK_COMB (@lem363111 B) (@lem363110 A B R a S' b P p1)). Qed.
Lemma lem363113 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term268 A B R a S' b P) = (term268 A B R a S' b P).
Proof. exact (fun_ext (fun p1 : A => @lem363112 A B R a S' b P p1)). Qed.
Lemma lem363114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363115 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term269 A B R a S' b P) = (term269 A B R a S' b P).
Proof. exact (MK_COMB (@lem363114 A) (@lem363113 A B R a S' b P)). Qed.
Lemma lem363118 {A B : Type'} (P : type1210 A B) (a : A) (b : B) : (term96 A B P a b) = (term96 A B P a b).
Proof. exact (eq_refl (term96 A B P a b)). Qed.
Lemma lem363119 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term280 A B R a S' b P) = (term280 A B R a S' b P).
Proof. exact (MK_COMB (@lem363118 A B P a b) (@lem363115 A B R a S' b P)). Qed.
Lemma lem363126 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (y : B) : (term130 A B S' b P a y) = (term130 A B S' b P a y).
Proof. exact (eq_refl (term130 A B S' b P a y)). Qed.
Lemma lem363127 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term132 A B S' b P a) = (term132 A B S' b P a).
Proof. exact (fun_ext (fun y : B => @lem363126 A B S' b P a y)). Qed.
Lemma lem363128 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363129 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term134 A B S' b P a) = (term134 A B S' b P a).
Proof. exact (MK_COMB (@lem363128 B) (@lem363127 A B S' b P a)). Qed.
Lemma lem363130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem363131 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term281 A B S' b P a) = (term281 A B S' b P a).
Proof. exact (MK_COMB (@lem363130) (@lem363129 A B S' b P a)). Qed.
Lemma lem363132 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term283 A B R a S' b P) = (term283 A B R a S' b P).
Proof. exact (MK_COMB (@lem363131 A B S' b P a) (@lem363119 A B R a S' b P)). Qed.
Lemma lem363135 {A B : Type'} (P : type1210 A B) (a : A) (b1 : B) : (term96 A B P a b1) = (term96 A B P a b1).
Proof. exact (eq_refl (term96 A B P a b1)). Qed.
Lemma lem363136 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term285 A B b1 R a S' b P) = (term285 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363135 A B P a b1) (@lem363132 A B R a S' b P)). Qed.
Lemma lem363137 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term52 A B P y b) = (term52 A B P y b).
Proof. exact (eq_refl (term52 A B P y b)). Qed.
Lemma lem363138 {A B : Type'} (P : type1210 A B) (y : A) : (term88 A B P y) = (term88 A B P y).
Proof. exact (fun_ext (fun b : B => @lem363137 A B P y b)). Qed.
Lemma lem363139 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem363140 {A B : Type'} (P : type1210 A B) (y : A) : (term62 A B P y) = (term62 A B P y).
Proof. exact (MK_COMB (@lem363139 B) (@lem363138 A B P y)). Qed.
Lemma lem363141 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem363142 {A B : Type'} (P : type1210 A B) (y : A) : (term71 A B P y) = (term71 A B P y).
Proof. exact (MK_COMB (@lem363141) (@lem363140 A B P y)). Qed.
Lemma lem363145 {A : Type'} (R : type1402 A) (y : A) (a : A) : (term72 A R y a) = (term72 A R y a).
Proof. exact (eq_refl (term72 A R y a)). Qed.
Lemma lem363146 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term74 A B R a P y) = (term74 A B R a P y).
Proof. exact (MK_COMB (@lem363145 A R y a) (@lem363142 A B P y)). Qed.
Lemma lem363147 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term76 A B R a P) = (term76 A B R a P).
Proof. exact (fun_ext (fun y : A => @lem363146 A B R a P y)). Qed.
Lemma lem363148 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363149 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term78 A B R a P) = (term78 A B R a P).
Proof. exact (MK_COMB (@lem363148 A) (@lem363147 A B R a P)). Qed.
Lemma lem363150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem363151 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term286 A B R a P) = (term286 A B R a P).
Proof. exact (MK_COMB (@lem363150) (@lem363149 A B R a P)). Qed.
Lemma lem363152 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term288 A B b1 R a S' b P) = (term288 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363151 A B R a P) (@lem363136 A B b1 R a S' b P)). Qed.
Lemma lem363155 {A B : Type'} (P : type1210 A B) (a0 : A) (b0 : B) : (term96 A B P a0 b0) = (term96 A B P a0 b0).
Proof. exact (eq_refl (term96 A B P a0 b0)). Qed.
Lemma lem363156 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term289 A B a0 b0 b1 R a S' b P) = (term289 A B a0 b0 b1 R a S' b P).
Proof. exact (MK_COMB (@lem363155 A B P a0 b0) (@lem363152 A B b1 R a S' b P)). Qed.
Lemma lem363157 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term291 A B b0 b1 R a S' b P) = (term291 A B b0 b1 R a S' b P).
Proof. exact (fun_ext (fun a0 : A => @lem363156 A B a0 b0 b1 R a S' b P)). Qed.
Lemma lem363158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363159 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term293 A B b0 b1 R a S' b P) = (term293 A B b0 b1 R a S' b P).
Proof. exact (MK_COMB (@lem363158 A) (@lem363157 A B b0 b1 R a S' b P)). Qed.
Lemma lem363160 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term295 A B b1 R a S' b P) = (term295 A B b1 R a S' b P).
Proof. exact (fun_ext (fun b0 : B => @lem363159 A B b0 b1 R a S' b P)). Qed.
Lemma lem363161 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363162 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term297 A B b1 R a S' b P) = (term297 A B b1 R a S' b P).
Proof. exact (MK_COMB (@lem363161 B) (@lem363160 A B b1 R a S' b P)). Qed.
Lemma lem363163 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term299 A B R a S' b P) = (term299 A B R a S' b P).
Proof. exact (fun_ext (fun b1 : B => @lem363162 A B b1 R a S' b P)). Qed.
Lemma lem363164 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363165 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term301 A B R a S' b P) = (term301 A B R a S' b P).
Proof. exact (MK_COMB (@lem363164 B) (@lem363163 A B R a S' b P)). Qed.
Lemma lem363166 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term303 A B a S' b P) = (term303 A B a S' b P).
Proof. exact (fun_ext (fun R : type1402 A => @lem363165 A B R a S' b P)). Qed.
Lemma lem363167 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem363168 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term305 A B a S' b P) = (term305 A B a S' b P).
Proof. exact (MK_COMB (@lem363167 A) (@lem363166 A B a S' b P)). Qed.
Lemma lem363169 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : (term307 A B S' b P) = (term307 A B S' b P).
Proof. exact (fun_ext (fun a : A => @lem363168 A B a S' b P)). Qed.
Lemma lem363170 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363171 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : (term309 A B S' b P) = (term309 A B S' b P).
Proof. exact (MK_COMB (@lem363170 A) (@lem363169 A B S' b P)). Qed.
Lemma lem363172 {A B : Type'} (b : B) (P : type1210 A B) : (term311 A B b P) = (term311 A B b P).
Proof. exact (fun_ext (fun S' : type1406 A B => @lem363171 A B S' b P)). Qed.
Lemma lem363173 {A B : Type'} : (@all (A -> B -> B -> Prop)) = (@all (A -> B -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> B -> Prop))). Qed.
Lemma lem363174 {A B : Type'} (b : B) (P : type1210 A B) : (term313 A B b P) = (term313 A B b P).
Proof. exact (MK_COMB (@lem363173 A B) (@lem363172 A B b P)). Qed.
Lemma lem363175 {A B : Type'} (P : type1210 A B) : (term315 A B P) = (term315 A B P).
Proof. exact (fun_ext (fun b : B => @lem363174 A B b P)). Qed.
Lemma lem363176 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363177 {A B : Type'} (P : type1210 A B) : (term317 A B P) = (term317 A B P).
Proof. exact (MK_COMB (@lem363176 B) (@lem363175 A B P)). Qed.
Lemma lem363178 {A B : Type'} : (term319 A B) = (term319 A B).
Proof. exact (fun_ext (fun P : type1210 A B => @lem363177 A B P)). Qed.
Lemma lem363179 {A B : Type'} : (@all ((prod A B) -> Prop)) = (@all ((prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((prod A B) -> Prop))). Qed.
Lemma lem363180 {A B : Type'} : (term321 A B) = (term321 A B).
Proof. exact (MK_COMB (@lem363179 A B) (@lem363178 A B)). Qed.
Lemma lem363281 {A B : Type'} : (term320 A B) = (term321 A B).
Proof. exact (TRANS (@lem363094 A B) (@lem363180 A B)). Qed.
Lemma lem363282 {A B : Type'} : (term321 A B) = (term320 A B).
Proof. exact (SYM (@lem363281 A B)). Qed.
Lemma lem363284 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term78 A B R a P.
Proof. exact (h1). Qed.
Lemma lem363286 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term134 A B S' b P a.
Proof. exact (h1). Qed.
Lemma lem363298 {B : Type'} (P : B -> Prop) : (term322 B P) = (term323 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem363299 {A B : Type'} (P : type1210 A B) (y : A) : (term71 A B P y) = (term324 A B P y).
Proof. exact (@lem363298 B (term88 A B P y)). Qed.
Lemma lem363300 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term89 A B P y b) = (term52 A B P y b).
Proof. exact (eq_refl (term89 A B P y b)). Qed.
Lemma lem363301 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem363303 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term126 A B P y b) = (term127 A B P y b).
Proof. exact (MK_COMB (@lem363301) (@lem363300 A B P y b)). Qed.
Lemma lem363304 {A B : Type'} (P : type1210 A B) (y : A) : (term325 A B P y) = (term326 A B P y).
Proof. exact (fun_ext (fun b : B => @lem363303 A B P y b)). Qed.
Lemma lem363305 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363306 {A B : Type'} (P : type1210 A B) (y : A) : (term324 A B P y) = (term327 A B P y).
Proof. exact (MK_COMB (@lem363305 B) (@lem363304 A B P y)). Qed.
Lemma lem363307 {A B : Type'} (P : type1210 A B) (y : A) : (term71 A B P y) = (term327 A B P y).
Proof. exact (TRANS (@lem363299 A B P y) (@lem363306 A B P y)). Qed.
Lemma lem363309 {A : Type'} (R : type1402 A) (y : A) (a : A) : (term328 A R y a) = (term328 A R y a).
Proof. exact (eq_refl (term328 A R y a)). Qed.
Lemma lem363310 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term329 A B R a P y) = (term330 A B R a P y).
Proof. exact (MK_COMB (@lem363309 A R y a) (@lem363307 A B P y)). Qed.
Lemma lem363311 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term74 A B R a P y) = (term329 A B R a P y).
Proof. exact (@lem17265 (R y a) (term71 A B P y)). Qed.
Lemma lem363312 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term74 A B R a P y) = (term330 A B R a P y).
Proof. exact (TRANS (@lem363311 A B R a P y) (@lem363310 A B R a P y)). Qed.
Lemma lem363313 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term76 A B R a P) = (term331 A B R a P).
Proof. exact (fun_ext (fun y : A => @lem363312 A B R a P y)). Qed.
Lemma lem363314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363371 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term78 A B R a P) = (term332 A B R a P).
Proof. exact (MK_COMB (@lem363314 A) (@lem363313 A B R a P)). Qed.
Lemma lem363372 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term332 A B R a P.
Proof. exact (EQ_MP (@lem363371 A B R a P) (@lem363284 A B R a P h1)). Qed.
Lemma lem363385 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (y : B) : (term130 A B S' b P a y) = (term333 A B S' b P a y).
Proof. exact (@lem17265 (S' a y b) (term127 A B P a y)). Qed.
Lemma lem363386 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term132 A B S' b P a) = (term334 A B S' b P a).
Proof. exact (fun_ext (fun y : B => @lem363385 A B S' b P a y)). Qed.
Lemma lem363387 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363440 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term134 A B S' b P a) = (term335 A B S' b P a).
Proof. exact (MK_COMB (@lem363387 B) (@lem363386 A B S' b P a)). Qed.
Lemma lem363441 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term335 A B S' b P a.
Proof. exact (EQ_MP (@lem363440 A B S' b P a) (@lem363286 A B S' b P a h1)). Qed.
Lemma lem363461 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term236 A B R a S' p1 p2 b) : term236 A B R a S' p1 p2 b.
Proof. exact (h1). Qed.
Lemma lem363467 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363484 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term127 A B P y b) = (term127 A B P y b).
Proof. exact (eq_refl (term127 A B P y b)). Qed.
Lemma lem363485 {A B : Type'} (P : type1210 A B) (y : A) : (term326 A B P y) = (term326 A B P y).
Proof. exact (fun_ext (fun b : B => @lem363484 A B P y b)). Qed.
Lemma lem363486 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363487 {A B : Type'} (P : type1210 A B) (y : A) : (term327 A B P y) = (term327 A B P y).
Proof. exact (MK_COMB (@lem363486 B) (@lem363485 A B P y)). Qed.
Lemma lem363496 {A : Type'} (R : type1402 A) (y : A) (a : A) : (term328 A R y a) = (term328 A R y a).
Proof. exact (eq_refl (term328 A R y a)). Qed.
Lemma lem363497 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term330 A B R a P y) = (term330 A B R a P y).
Proof. exact (MK_COMB (@lem363496 A R y a) (@lem363487 A B P y)). Qed.
Lemma lem363498 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term331 A B R a P) = (term331 A B R a P).
Proof. exact (fun_ext (fun y : A => @lem363497 A B R a P y)). Qed.
Lemma lem363499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363500 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term332 A B R a P) = (term332 A B R a P).
Proof. exact (MK_COMB (@lem363499 A) (@lem363498 A B R a P)). Qed.
Lemma lem363501 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term332 A B R a P.
Proof. exact (EQ_MP (@lem363500 A B R a P) (@lem363372 A B R a P h1)). Qed.
Lemma lem363530 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (y : B) : (term333 A B S' b P a y) = (term333 A B S' b P a y).
Proof. exact (eq_refl (term333 A B S' b P a y)). Qed.
Lemma lem363531 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term334 A B S' b P a) = (term334 A B S' b P a).
Proof. exact (fun_ext (fun y : B => @lem363530 A B S' b P a y)). Qed.
Lemma lem363532 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363533 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term335 A B S' b P a) = (term335 A B S' b P a).
Proof. exact (MK_COMB (@lem363532 B) (@lem363531 A B S' b P a)). Qed.
Lemma lem363534 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term335 A B S' b P a.
Proof. exact (EQ_MP (@lem363533 A B S' b P a) (@lem363441 A B S' b P a h1)). Qed.
Lemma lem363566 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term236 A B R a S' p1 p2 b) : term236 A B R a S' p1 p2 b.
Proof. exact (h1). Qed.
Lemma lem363574 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363576 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : term336 A B a S' p1 p2 b.
Proof. exact (h1). Qed.
Lemma lem363584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem363585 {B : Type'} (P : Prop) (Q : B -> Prop) : (term337 B P Q) = (term338 B P Q).
Proof. exact (@lem363584 B P Q). Qed.
Lemma lem363586 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term339 A B R a P y) = (term340 A B R a P y).
Proof. exact (@lem363585 B (term341 A R y a) (term326 A B P y)). Qed.
Lemma lem363587 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term342 A B P y b) = (term127 A B P y b).
Proof. exact (eq_refl (term342 A B P y b)). Qed.
Lemma lem363588 {A B : Type'} (P : type1210 A B) (y : A) : (term343 A B P y) = (term326 A B P y).
Proof. exact (fun_ext (fun b : B => @lem363587 A B P y b)). Qed.
Lemma lem363589 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363590 {A B : Type'} (P : type1210 A B) (y : A) : (term344 A B P y) = (term327 A B P y).
Proof. exact (MK_COMB (@lem363589 B) (@lem363588 A B P y)). Qed.
Lemma lem363591 {A : Type'} (R : type1402 A) (y : A) (a : A) : (term328 A R y a) = (term328 A R y a).
Proof. exact (eq_refl (term328 A R y a)). Qed.
Lemma lem363592 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term339 A B R a P y) = (term330 A B R a P y).
Proof. exact (MK_COMB (@lem363591 A R y a) (@lem363590 A B P y)). Qed.
Lemma lem363593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem363594 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term345 A B R a P y) = (term346 A B R a P y).
Proof. exact (MK_COMB (@lem363593) (@lem363592 A B R a P y)). Qed.
Lemma lem363595 {A B : Type'} (P : type1210 A B) (y : A) (b : B) : (term342 A B P y b) = (term127 A B P y b).
Proof. exact (eq_refl (term342 A B P y b)). Qed.
Lemma lem363596 {A : Type'} (R : type1402 A) (y : A) (a : A) : (term328 A R y a) = (term328 A R y a).
Proof. exact (eq_refl (term328 A R y a)). Qed.
Lemma lem363597 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) (b : B) : (term347 A B R a P y b) = (term348 A B R a P y b).
Proof. exact (MK_COMB (@lem363596 A R y a) (@lem363595 A B P y b)). Qed.
Lemma lem363598 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term349 A B R a P y) = (term350 A B R a P y).
Proof. exact (fun_ext (fun b : B => @lem363597 A B R a P y b)). Qed.
Lemma lem363599 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363600 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term340 A B R a P y) = (term351 A B R a P y).
Proof. exact (MK_COMB (@lem363599 B) (@lem363598 A B R a P y)). Qed.
Lemma lem363601 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : ((term339 A B R a P y) = (term340 A B R a P y)) = ((term330 A B R a P y) = (term351 A B R a P y)).
Proof. exact (MK_COMB (@lem363594 A B R a P y) (@lem363600 A B R a P y)). Qed.
Lemma lem363602 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term330 A B R a P y) = (term351 A B R a P y).
Proof. exact (EQ_MP (@lem363601 A B R a P y) (@lem363586 A B R a P y)). Qed.
Lemma lem363603 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term331 A B R a P) = (term352 A B R a P).
Proof. exact (fun_ext (fun y : A => @lem363602 A B R a P y)). Qed.
Lemma lem363604 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363605 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term332 A B R a P) = (term353 A B R a P).
Proof. exact (MK_COMB (@lem363604 A) (@lem363603 A B R a P)). Qed.
Lemma lem363612 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) (b : B) : (term348 A B R a P y b) = (term348 A B R a P y b).
Proof. exact (eq_refl (term348 A B R a P y b)). Qed.
Lemma lem363613 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term350 A B R a P y) = (term350 A B R a P y).
Proof. exact (fun_ext (fun b : B => @lem363612 A B R a P y b)). Qed.
Lemma lem363614 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363615 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (y : A) : (term351 A B R a P y) = (term351 A B R a P y).
Proof. exact (MK_COMB (@lem363614 B) (@lem363613 A B R a P y)). Qed.
Lemma lem363616 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term352 A B R a P) = (term352 A B R a P).
Proof. exact (fun_ext (fun y : A => @lem363615 A B R a P y)). Qed.
Lemma lem363617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem363618 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term353 A B R a P) = (term353 A B R a P).
Proof. exact (MK_COMB (@lem363617 A) (@lem363616 A B R a P)). Qed.
Lemma lem363619 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) : (term332 A B R a P) = (term353 A B R a P).
Proof. exact (TRANS (@lem363605 A B R a P) (@lem363618 A B R a P)). Qed.
Lemma lem363620 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term353 A B R a P.
Proof. exact (EQ_MP (@lem363619 A B R a P) (@lem363501 A B R a P h1)). Qed.
Lemma lem363645 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363649 {A : Type'} (R : type1402 A) (p1 : A) (a : A) (h1 : R p1 a) : R p1 a.
Proof. exact (h1). Qed.
Lemma lem363703 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (y : B) : (term333 A B S' b P a y) = (term333 A B S' b P a y).
Proof. exact (eq_refl (term333 A B S' b P a y)). Qed.
Lemma lem363704 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term334 A B S' b P a) = (term334 A B S' b P a).
Proof. exact (fun_ext (fun y : B => @lem363703 A B S' b P a y)). Qed.
Lemma lem363705 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem363707 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : (term335 A B S' b P a) = (term335 A B S' b P a).
Proof. exact (MK_COMB (@lem363705 B) (@lem363704 A B S' b P a)). Qed.
Lemma lem363708 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term335 A B S' b P a.
Proof. exact (EQ_MP (@lem363707 A B S' b P a) (@lem363534 A B S' b P a h1)). Qed.
Lemma lem363716 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363725 {A B : Type'} (_7857 : A) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term354 A B R a P _7857.
Proof. exact (@lem363620 A B R a P h1 _7857). Qed.
Lemma lem363726 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (_7857 : A) : (term354 A B R a P _7857) = (term351 A B R a P _7857).
Proof. exact (eq_refl (term354 A B R a P _7857)). Qed.
Lemma lem363727 {A B : Type'} (_7857 : A) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term351 A B R a P _7857.
Proof. exact (EQ_MP (@lem363726 A B R a P _7857) (@lem363725 A B _7857 R a P h1)). Qed.
Lemma lem363728 {A B : Type'} (_7857 : A) (_7858 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term355 A B R a P _7857 _7858.
Proof. exact (@lem363727 A B _7857 R a P h1 _7858). Qed.
Lemma lem363729 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (_7857 : A) (_7858 : B) : (term355 A B R a P _7857 _7858) = (term348 A B R a P _7857 _7858).
Proof. exact (eq_refl (term355 A B R a P _7857 _7858)). Qed.
Lemma lem363740 {A B : Type'} (_7862 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term356 A B S' b P a _7862.
Proof. exact (@lem363708 A B S' b P a h1 _7862). Qed.
Lemma lem363741 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (_7862 : B) : (term356 A B S' b P a _7862) = (term333 A B S' b P a _7862).
Proof. exact (eq_refl (term356 A B S' b P a _7862)). Qed.
Lemma lem363750 {A B : Type'} (_7857 : A) (_7858 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term348 A B R a P _7857 _7858.
Proof. exact (EQ_MP (@lem363729 A B R a P _7857 _7858) (@lem363728 A B _7857 _7858 R a P h1)). Qed.
Lemma lem363762 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363764 {A : Type'} (R : type1402 A) (p1 : A) (a : A) (h1 : R p1 a) : R p1 a.
Proof. exact (h1). Qed.
Lemma lem363784 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363786 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : p1 = a.
Proof. exact (proj1 (@lem363576 A B a S' p1 p2 b h1)). Qed.
Lemma lem363788 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : S' p1 p2 b.
Proof. exact (proj2 (@lem363576 A B a S' p1 p2 b h1)). Qed.
Lemma lem363858 {A B : Type'} (_7862 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term333 A B S' b P a _7862.
Proof. exact (EQ_MP (@lem363741 A B S' b P a _7862) (@lem363740 A B _7862 S' b P a h1)). Qed.
Lemma lem363873 {A B : Type'} (P : type1210 A B) (p2 : B) : (term357 A B P p2) = (term357 A B P p2).
Proof. exact (eq_refl (term357 A B P p2)). Qed.
Lemma lem363874 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : (term358 A B P p2 p1) = (term358 A B P p2 a).
Proof. exact (MK_COMB (@lem363873 A B P p2) (@lem363786 A B a S' p1 p2 b h1)). Qed.
Lemma lem363875 {A B : Type'} (P : type1210 A B) (a : A) (p2 : B) : (term358 A B P p2 a) = (term52 A B P a p2).
Proof. exact (eq_refl (term358 A B P p2 a)). Qed.
Lemma lem363876 {A B : Type'} (P : type1210 A B) (p2 : B) (p1 : A) : (term359 A B P p2 p1) = (term359 A B P p2 p1).
Proof. exact (eq_refl (term359 A B P p2 p1)). Qed.
Lemma lem363877 {A B : Type'} (p1 : A) (P : type1210 A B) (a : A) (p2 : B) : ((term358 A B P p2 p1) = (term358 A B P p2 a)) = ((term358 A B P p2 p1) = (term52 A B P a p2)).
Proof. exact (MK_COMB (@lem363876 A B P p2 p1) (@lem363875 A B P a p2)). Qed.
Lemma lem363878 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) : (term358 A B P p2 p1) = (term52 A B P p1 p2).
Proof. exact (eq_refl (term358 A B P p2 p1)). Qed.
Lemma lem363879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem363880 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) : (term359 A B P p2 p1) = (term360 A B P p1 p2).
Proof. exact (MK_COMB (@lem363879) (@lem363878 A B P p1 p2)). Qed.
Lemma lem363881 {A B : Type'} (P : type1210 A B) (a : A) (p2 : B) : (term52 A B P a p2) = (term52 A B P a p2).
Proof. exact (eq_refl (term52 A B P a p2)). Qed.
Lemma lem363882 {A B : Type'} (p1 : A) (P : type1210 A B) (a : A) (p2 : B) : ((term358 A B P p2 p1) = (term52 A B P a p2)) = ((term52 A B P p1 p2) = (term52 A B P a p2)).
Proof. exact (MK_COMB (@lem363880 A B P p1 p2) (@lem363881 A B P a p2)). Qed.
Lemma lem363883 {A B : Type'} (p1 : A) (P : type1210 A B) (a : A) (p2 : B) : ((term358 A B P p2 p1) = (term358 A B P p2 a)) = ((term52 A B P p1 p2) = (term52 A B P a p2)).
Proof. exact (TRANS (@lem363877 A B p1 P a p2) (@lem363882 A B p1 P a p2)). Qed.
Lemma lem363884 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : (term52 A B P p1 p2) = (term52 A B P a p2).
Proof. exact (EQ_MP (@lem363883 A B p1 P a p2) (@lem363874 A B P a S' p1 p2 b h1)). Qed.
Lemma lem363886 {A B : Type'} (S' : type1406 A B) (p2 : B) (b : B) : (term361 A B S' p2 b) = (term361 A B S' p2 b).
Proof. exact (eq_refl (term361 A B S' p2 b)). Qed.
Lemma lem363887 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : (term362 A B S' p2 b p1) = (term362 A B S' p2 b a).
Proof. exact (MK_COMB (@lem363886 A B S' p2 b) (@lem363786 A B a S' p1 p2 b h1)). Qed.
Lemma lem363888 {A B : Type'} (S' : type1406 A B) (a : A) (p2 : B) (b : B) : (term362 A B S' p2 b a) = (S' a p2 b).
Proof. exact (eq_refl (term362 A B S' p2 b a)). Qed.
Lemma lem363889 {A B : Type'} (S' : type1406 A B) (p2 : B) (b : B) (p1 : A) : (term363 A B S' p2 b p1) = (term363 A B S' p2 b p1).
Proof. exact (eq_refl (term363 A B S' p2 b p1)). Qed.
Lemma lem363890 {A B : Type'} (p1 : A) (S' : type1406 A B) (a : A) (p2 : B) (b : B) : ((term362 A B S' p2 b p1) = (term362 A B S' p2 b a)) = ((term362 A B S' p2 b p1) = (S' a p2 b)).
Proof. exact (MK_COMB (@lem363889 A B S' p2 b p1) (@lem363888 A B S' a p2 b)). Qed.
Lemma lem363891 {A B : Type'} (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) : (term362 A B S' p2 b p1) = (S' p1 p2 b).
Proof. exact (eq_refl (term362 A B S' p2 b p1)). Qed.
Lemma lem363892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem363893 {A B : Type'} (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) : (term363 A B S' p2 b p1) = (term364 A B S' p1 p2 b).
Proof. exact (MK_COMB (@lem363892) (@lem363891 A B S' p1 p2 b)). Qed.
Lemma lem363894 {A B : Type'} (S' : type1406 A B) (a : A) (p2 : B) (b : B) : (S' a p2 b) = (S' a p2 b).
Proof. exact (eq_refl (S' a p2 b)). Qed.
Lemma lem363895 {A B : Type'} (p1 : A) (S' : type1406 A B) (a : A) (p2 : B) (b : B) : ((term362 A B S' p2 b p1) = (S' a p2 b)) = ((S' p1 p2 b) = (S' a p2 b)).
Proof. exact (MK_COMB (@lem363893 A B S' p1 p2 b) (@lem363894 A B S' a p2 b)). Qed.
Lemma lem363896 {A B : Type'} (p1 : A) (S' : type1406 A B) (a : A) (p2 : B) (b : B) : ((term362 A B S' p2 b p1) = (term362 A B S' p2 b a)) = ((S' p1 p2 b) = (S' a p2 b)).
Proof. exact (TRANS (@lem363890 A B p1 S' a p2 b) (@lem363895 A B p1 S' a p2 b)). Qed.
Lemma lem363897 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : (S' p1 p2 b) = (S' a p2 b).
Proof. exact (EQ_MP (@lem363896 A B p1 S' a p2 b) (@lem363887 A B a S' p1 p2 b h1)). Qed.
Lemma lem363900 {A : Type'} (R : type1402 A) (p1 : A) (a : A) (h1 : R p1 a) : R p1 a.
Proof. exact (h1). Qed.
Lemma lem363901 {A : Type'} (R : type1402 A) (p1 : A) (a : A) (h1 : R p1 a) : term365 A R p1 a.
Proof. exact (fun h0 : term341 A R p1 a => @lem363900 A R p1 a h1). Qed.
Lemma lem363903 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363904 {A : Type'} (R : type1402 A) (p1 : A) (a : A) : (term365 A R p1 a) = (R p1 a).
Proof. exact (@lem363903 (R p1 a)). Qed.
Lemma lem363905 {A : Type'} (R : type1402 A) (p1 : A) (a : A) (h1 : R p1 a) : R p1 a.
Proof. exact (EQ_MP (@lem363904 A R p1 a) (@lem363901 A R p1 a h1)). Qed.
Lemma lem363907 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (h1). Qed.
Lemma lem363908 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term367 A B P p1 p2.
Proof. exact (fun h0 : term127 A B P p1 p2 => @lem363907 A B P p1 p2 h1). Qed.
Lemma lem363910 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363911 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) : (term367 A B P p1 p2) = (term52 A B P p1 p2).
Proof. exact (@lem363910 (term52 A B P p1 p2)). Qed.
Lemma lem363912 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) (h1 : term52 A B P p1 p2) : term52 A B P p1 p2.
Proof. exact (EQ_MP (@lem363911 A B P p1 p2) (@lem363908 A B P p1 p2 h1)). Qed.
Lemma lem363914 (a : Prop) (b : Prop) : (term368 a b) = (term369 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem363915 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (_7857 : A) (_7858 : B) : (term348 A B R a P _7857 _7858) = (term370 A B R a P _7857 _7858).
Proof. exact (@lem363914 (R _7857 a) (term52 A B P _7857 _7858)). Qed.
Lemma lem363917 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem363918 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (_7857 : A) (_7858 : B) : (term370 A B R a P _7857 _7858) = (term371 A B R a P _7857 _7858).
Proof. exact (@lem363917 (term372 A B R a P _7857 _7858)). Qed.
Lemma lem363919 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (_7857 : A) (_7858 : B) : (term348 A B R a P _7857 _7858) = (term371 A B R a P _7857 _7858).
Proof. exact (TRANS (@lem363915 A B R a P _7857 _7858) (@lem363918 A B R a P _7857 _7858)). Qed.
Lemma lem363921 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term52 A B P p1 p2) (h2 : R p1 a) : term372 A B R a P p1 p2.
Proof. exact (conj (@lem363905 A R p1 a h2) (@lem363912 A B P p1 p2 h1)). Qed.
Lemma lem363923 {A B : Type'} (_7857 : A) (_7858 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term371 A B R a P _7857 _7858.
Proof. exact (EQ_MP (@lem363919 A B R a P _7857 _7858) (@lem363750 A B _7857 _7858 R a P h1)). Qed.
Lemma lem363924 {A B : Type'} (_7857 : A) (_7858 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term371 A B R a P _7857 _7858.
Proof. exact (@lem363923 A B _7857 _7858 R a P h1). Qed.
Lemma lem363925 {A B : Type'} (p1 : A) (p2 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term371 A B R a P p1 p2.
Proof. exact (@lem363924 A B p1 p2 R a P h1). Qed.
Lemma lem363928 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (@lem363925 A B p1 p2 R a P h1 (@lem363921 A B P p2 R p1 a h2 h3)). Qed.
Lemma lem363929 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : term373.
Proof. exact (fun h0 : ~ False => @lem363928 A B P p2 R p1 a h1 h2 h3). Qed.
Lemma lem363931 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363932 : term373 = False.
Proof. exact (@lem363931 False). Qed.
Lemma lem363933 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363932) (@lem363929 A B P p2 R p1 a h1 h2 h3)). Qed.
Lemma lem363935 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : S' a p2 b.
Proof. exact (EQ_MP (@lem363897 A B a S' p1 p2 b h1) (@lem363788 A B a S' p1 p2 b h1)). Qed.
Lemma lem363936 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : term374 A B S' a p2 b.
Proof. exact (fun h0 : term375 A B S' a p2 b => @lem363935 A B a S' p1 p2 b h1). Qed.
Lemma lem363938 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363939 {A B : Type'} (S' : type1406 A B) (a : A) (p2 : B) (b : B) : (term374 A B S' a p2 b) = (S' a p2 b).
Proof. exact (@lem363938 (S' a p2 b)). Qed.
Lemma lem363940 {A B : Type'} (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term336 A B a S' p1 p2 b) : S' a p2 b.
Proof. exact (EQ_MP (@lem363939 A B S' a p2 b) (@lem363936 A B a S' p1 p2 b h1)). Qed.
Lemma lem363942 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term52 A B P p1 p2) (h2 : term336 A B a S' p1 p2 b) : term52 A B P a p2.
Proof. exact (EQ_MP (@lem363884 A B P a S' p1 p2 b h2) (@lem363784 A B P p1 p2 h1)). Qed.
Lemma lem363943 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term52 A B P p1 p2) (h2 : term336 A B a S' p1 p2 b) : term367 A B P a p2.
Proof. exact (fun h0 : term127 A B P a p2 => @lem363942 A B P a S' p1 p2 b h1 h2). Qed.
Lemma lem363945 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363946 {A B : Type'} (P : type1210 A B) (a : A) (p2 : B) : (term367 A B P a p2) = (term52 A B P a p2).
Proof. exact (@lem363945 (term52 A B P a p2)). Qed.
Lemma lem363947 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term52 A B P p1 p2) (h2 : term336 A B a S' p1 p2 b) : term52 A B P a p2.
Proof. exact (EQ_MP (@lem363946 A B P a p2) (@lem363943 A B P a S' p1 p2 b h1 h2)). Qed.
Lemma lem363949 (a : Prop) (b : Prop) : (term368 a b) = (term369 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem363950 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (_7862 : B) : (term333 A B S' b P a _7862) = (term376 A B S' b P a _7862).
Proof. exact (@lem363949 (S' a _7862 b) (term52 A B P a _7862)). Qed.
Lemma lem363952 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem363953 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (_7862 : B) : (term376 A B S' b P a _7862) = (term377 A B S' b P a _7862).
Proof. exact (@lem363952 (term378 A B S' b P a _7862)). Qed.
Lemma lem363954 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (_7862 : B) : (term333 A B S' b P a _7862) = (term377 A B S' b P a _7862).
Proof. exact (TRANS (@lem363950 A B S' b P a _7862) (@lem363953 A B S' b P a _7862)). Qed.
Lemma lem363956 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term52 A B P p1 p2) (h2 : term336 A B a S' p1 p2 b) : term378 A B S' b P a p2.
Proof. exact (conj (@lem363940 A B a S' p1 p2 b h2) (@lem363947 A B P a S' p1 p2 b h1 h2)). Qed.
Lemma lem363958 {A B : Type'} (_7862 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term377 A B S' b P a _7862.
Proof. exact (EQ_MP (@lem363954 A B S' b P a _7862) (@lem363858 A B _7862 S' b P a h1)). Qed.
Lemma lem363959 {A B : Type'} (_7862 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term377 A B S' b P a _7862.
Proof. exact (@lem363958 A B _7862 S' b P a h1). Qed.
Lemma lem363960 {A B : Type'} (p2 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term134 A B S' b P a) : term377 A B S' b P a p2.
Proof. exact (@lem363959 A B p2 S' b P a h1). Qed.
Lemma lem363963 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : False.
Proof. exact (@lem363960 A B p2 S' b P a h1 (@lem363956 A B P a S' p1 p2 b h2 h3)). Qed.
Lemma lem363964 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : term373.
Proof. exact (fun h0 : ~ False => @lem363963 A B P a S' p1 p2 b h1 h2 h3). Qed.
Lemma lem363966 (p : Prop) : (term366 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem363967 : term373 = False.
Proof. exact (@lem363966 False). Qed.
Lemma lem363969 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363967) (@lem363964 A B P a S' p1 p2 b h1 h2 h3)). Qed.
Lemma lem363970 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363969 A B P a S' p1 p2 b h1 h2 h3) (fun h4 : False => @lem363784 A B P p1 p2 h2)). Qed.
Lemma lem363971 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363970 A B P a S' p1 p2 b h1 h2 h3) (@lem363784 A B P p1 p2 h2)). Qed.
Lemma lem363972 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (R p1 a) = False.
Proof. exact (prop_ext (fun h4 : R p1 a => @lem363933 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363764 A R p1 a h3)). Qed.
Lemma lem363973 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363972 A B P p2 R p1 a h1 h2 h3) (@lem363764 A R p1 a h3)). Qed.
Lemma lem363974 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363973 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363762 A B P p1 p2 h2)). Qed.
Lemma lem363975 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363974 A B P p2 R p1 a h1 h2 h3) (@lem363762 A B P p1 p2 h2)). Qed.
Lemma lem363976 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363971 A B P a S' p1 p2 b h1 h2 h3) (fun h4 : False => @lem363716 A B P p1 p2 h2)). Qed.
Lemma lem363977 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363976 A B P a S' p1 p2 b h1 h2 h3) (@lem363716 A B P p1 p2 h2)). Qed.
Lemma lem363978 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (R p1 a) = False.
Proof. exact (prop_ext (fun h4 : R p1 a => @lem363975 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363649 A R p1 a h3)). Qed.
Lemma lem363979 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363978 A B P p2 R p1 a h1 h2 h3) (@lem363649 A R p1 a h3)). Qed.
Lemma lem363980 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363979 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363645 A B P p1 p2 h2)). Qed.
Lemma lem363981 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363980 A B P p2 R p1 a h1 h2 h3) (@lem363645 A B P p1 p2 h2)). Qed.
Lemma lem363982 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363977 A B P a S' p1 p2 b h1 h2 h3) (fun h4 : False => @lem363716 A B P p1 p2 h2)). Qed.
Lemma lem363983 {A B : Type'} (P : type1210 A B) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term134 A B S' b P a) (h2 : term52 A B P p1 p2) (h3 : term336 A B a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363982 A B P a S' p1 p2 b h1 h2 h3) (@lem363716 A B P p1 p2 h2)). Qed.
Lemma lem363984 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (R p1 a) = False.
Proof. exact (prop_ext (fun h4 : R p1 a => @lem363981 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363649 A R p1 a h3)). Qed.
Lemma lem363985 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363984 A B P p2 R p1 a h1 h2 h3) (@lem363649 A R p1 a h3)). Qed.
Lemma lem363986 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h4 : term52 A B P p1 p2 => @lem363985 A B P p2 R p1 a h1 h2 h3) (fun h4 : False => @lem363645 A B P p1 p2 h2)). Qed.
Lemma lem363987 {A B : Type'} (P : type1210 A B) (p2 : B) (R : type1402 A) (p1 : A) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P p1 p2) (h3 : R p1 a) : False.
Proof. exact (EQ_MP (@lem363986 A B P p2 R p1 a h1 h2 h3) (@lem363645 A B P p1 p2 h2)). Qed.
Lemma lem363988 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : False.
Proof. exact (or_elim (@lem363566 A B R a S' p1 p2 b h4) (fun h0 : R p1 a => @lem363987 A B P p2 R p1 a h1 h3 h0) (fun h0 : term336 A B a S' p1 p2 b => @lem363983 A B P a S' p1 p2 b h2 h3 h0)). Qed.
Lemma lem363989 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h5 : term52 A B P p1 p2 => @lem363988 A B P R a S' p1 p2 b h1 h2 h3 h4) (fun h5 : False => @lem363574 A B P p1 p2 h3)). Qed.
Lemma lem363990 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363989 A B P R a S' p1 p2 b h1 h2 h3 h4) (@lem363574 A B P p1 p2 h3)). Qed.
Lemma lem363991 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : (term236 A B R a S' p1 p2 b) = False.
Proof. exact (prop_ext (fun h5 : term236 A B R a S' p1 p2 b => @lem363990 A B P R a S' p1 p2 b h1 h2 h3 h4) (fun h5 : False => @lem363566 A B R a S' p1 p2 b h4)). Qed.
Lemma lem363992 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363991 A B P R a S' p1 p2 b h1 h2 h3 h4) (@lem363566 A B R a S' p1 p2 b h4)). Qed.
Lemma lem363993 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : (term52 A B P p1 p2) = False.
Proof. exact (prop_ext (fun h5 : term52 A B P p1 p2 => @lem363992 A B P R a S' p1 p2 b h1 h2 h3 h4) (fun h5 : False => @lem363467 A B P p1 p2 h3)). Qed.
Lemma lem363994 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363993 A B P R a S' p1 p2 b h1 h2 h3 h4) (@lem363467 A B P p1 p2 h3)). Qed.
Lemma lem363995 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : (term236 A B R a S' p1 p2 b) = False.
Proof. exact (prop_ext (fun h5 : term236 A B R a S' p1 p2 b => @lem363994 A B P R a S' p1 p2 b h1 h2 h3 h4) (fun h5 : False => @lem363461 A B R a S' p1 p2 b h4)). Qed.
Lemma lem363996 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P p1 p2) (h4 : term236 A B R a S' p1 p2 b) : False.
Proof. exact (EQ_MP (@lem363995 A B P R a S' p1 p2 b h1 h2 h3 h4) (@lem363461 A B R a S' p1 p2 b h4)). Qed.
Lemma lem363997 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term236 A B R a S' p1 p2 b) : term379 A B P p1 p2.
Proof. exact (fun h0 : term52 A B P p1 p2 => @lem363996 A B P R a S' p1 p2 b h1 h2 h0 h3). Qed.
Lemma lem363998 {A B : Type'} (P : type1210 A B) (p1 : A) (p2 : B) : (term379 A B P p1 p2) = (term127 A B P p1 p2).
Proof. exact (@lem69 (term52 A B P p1 p2)). Qed.
Lemma lem363999 {A B : Type'} (P : type1210 A B) (R : type1402 A) (a : A) (S' : type1406 A B) (p1 : A) (p2 : B) (b : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term236 A B R a S' p1 p2 b) : term127 A B P p1 p2.
Proof. exact (EQ_MP (@lem363998 A B P p1 p2) (@lem363997 A B P R a S' p1 p2 b h1 h2 h3)). Qed.
Lemma lem364000 {A B : Type'} (p1 : A) (p2 : B) (R : type1402 A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) : term265 A B R a S' b P p1 p2.
Proof. exact (fun h0 : term236 A B R a S' p1 p2 b => @lem363999 A B P R a S' p1 p2 b h1 h2 h0). Qed.
Lemma lem364005 {A B : Type'} (p1 : A) (R : type1402 A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) : term267 A B R a S' b P p1.
Proof. exact (fun p2 : B => @lem364000 A B p1 p2 R S' b P a h1 h2). Qed.
Lemma lem364010 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) : term269 A B R a S' b P.
Proof. exact (fun p1 : A => @lem364005 A B p1 R S' b P a h1 h2). Qed.
Lemma lem364011 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) : term280 A B R a S' b P.
Proof. exact (fun h0 : term52 A B P a b => @lem364010 A B R S' b P a h1 h2). Qed.
Lemma lem364012 {A B : Type'} (S' : type1406 A B) (b : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term283 A B R a S' b P.
Proof. exact (fun h0 : term134 A B S' b P a => @lem364011 A B R S' b P a h1 h0). Qed.
Lemma lem364013 {A B : Type'} (b1 : B) (S' : type1406 A B) (b : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term78 A B R a P) : term285 A B b1 R a S' b P.
Proof. exact (fun h0 : term52 A B P a b1 => @lem364012 A B S' b R a P h1). Qed.
Lemma lem364014 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term288 A B b1 R a S' b P.
Proof. exact (fun h0 : term78 A B R a P => @lem364013 A B b1 S' b R a P h0). Qed.
Lemma lem364015 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term289 A B a0 b0 b1 R a S' b P.
Proof. exact (fun h0 : term52 A B P a0 b0 => @lem364014 A B b1 R a S' b P). Qed.
Lemma lem364020 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term293 A B b0 b1 R a S' b P.
Proof. exact (fun a0 : A => @lem364015 A B a0 b0 b1 R a S' b P). Qed.
Lemma lem364025 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term297 A B b1 R a S' b P.
Proof. exact (fun b0 : B => @lem364020 A B b0 b1 R a S' b P). Qed.
Lemma lem364030 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term301 A B R a S' b P.
Proof. exact (fun b1 : B => @lem364025 A B b1 R a S' b P). Qed.
Lemma lem364035 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term305 A B a S' b P.
Proof. exact (fun R : type1402 A => @lem364030 A B R a S' b P). Qed.
Lemma lem364040 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : term309 A B S' b P.
Proof. exact (fun a : A => @lem364035 A B a S' b P). Qed.
Lemma lem364045 {A B : Type'} (b : B) (P : type1210 A B) : term313 A B b P.
Proof. exact (fun S' : type1406 A B => @lem364040 A B S' b P). Qed.
Lemma lem364050 {A B : Type'} (P : type1210 A B) : term317 A B P.
Proof. exact (fun b : B => @lem364045 A B b P). Qed.
Lemma lem364055 {A B : Type'} : term321 A B.
Proof. exact (fun P : type1210 A B => @lem364050 A B P). Qed.
Lemma lem364056 {A B : Type'} : term320 A B.
Proof. exact (EQ_MP (@lem363282 A B) (@lem364055 A B)). Qed.
Lemma lem364057 {A B : Type'} (P : type1210 A B) : term380 A B P.
Proof. exact (@lem364056 A B P). Qed.
Lemma lem364058 {A B : Type'} (P : type1210 A B) : (term380 A B P) = (term316 A B P).
Proof. exact (eq_refl (term380 A B P)). Qed.
Lemma lem364059 {A B : Type'} (P : type1210 A B) : term316 A B P.
Proof. exact (EQ_MP (@lem364058 A B P) (@lem364057 A B P)). Qed.
Lemma lem364060 {A B : Type'} (P : type1210 A B) (b : B) : term381 A B P b.
Proof. exact (@lem364059 A B P b). Qed.
Lemma lem364061 {A B : Type'} (b : B) (P : type1210 A B) : (term381 A B P b) = (term312 A B b P).
Proof. exact (eq_refl (term381 A B P b)). Qed.
Lemma lem364062 {A B : Type'} (b : B) (P : type1210 A B) : term312 A B b P.
Proof. exact (EQ_MP (@lem364061 A B b P) (@lem364060 A B P b)). Qed.
Lemma lem364063 {A B : Type'} (b : B) (P : type1210 A B) (S' : type1406 A B) : term382 A B b P S'.
Proof. exact (@lem364062 A B b P S'). Qed.
Lemma lem364064 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : (term382 A B b P S') = (term308 A B S' b P).
Proof. exact (eq_refl (term382 A B b P S')). Qed.
Lemma lem364065 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) : term308 A B S' b P.
Proof. exact (EQ_MP (@lem364064 A B S' b P) (@lem364063 A B b P S')). Qed.
Lemma lem364066 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) : term383 A B S' b P a.
Proof. exact (@lem364065 A B S' b P a). Qed.
Lemma lem364067 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term383 A B S' b P a) = (term304 A B a S' b P).
Proof. exact (eq_refl (term383 A B S' b P a)). Qed.
Lemma lem364068 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term304 A B a S' b P.
Proof. exact (EQ_MP (@lem364067 A B a S' b P) (@lem364066 A B S' b P a)). Qed.
Lemma lem364069 {A B : Type'} (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (R : type1402 A) : term384 A B a S' b P R.
Proof. exact (@lem364068 A B a S' b P R). Qed.
Lemma lem364070 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term384 A B a S' b P R) = (term300 A B R a S' b P).
Proof. exact (eq_refl (term384 A B a S' b P R)). Qed.
Lemma lem364071 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term300 A B R a S' b P.
Proof. exact (EQ_MP (@lem364070 A B R a S' b P) (@lem364069 A B a S' b P R)). Qed.
Lemma lem364072 {A B : Type'} (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (b1 : B) : term385 A B R a S' b P b1.
Proof. exact (@lem364071 A B R a S' b P b1). Qed.
Lemma lem364073 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term385 A B R a S' b P b1) = (term296 A B b1 R a S' b P).
Proof. exact (eq_refl (term385 A B R a S' b P b1)). Qed.
Lemma lem364074 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term296 A B b1 R a S' b P.
Proof. exact (EQ_MP (@lem364073 A B b1 R a S' b P) (@lem364072 A B R a S' b P b1)). Qed.
Lemma lem364075 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (b0 : B) : term386 A B b1 R a S' b P b0.
Proof. exact (@lem364074 A B b1 R a S' b P b0). Qed.
Lemma lem364076 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term386 A B b1 R a S' b P b0) = (term292 A B b0 b1 R a S' b P).
Proof. exact (eq_refl (term386 A B b1 R a S' b P b0)). Qed.
Lemma lem364077 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term292 A B b0 b1 R a S' b P.
Proof. exact (EQ_MP (@lem364076 A B b0 b1 R a S' b P) (@lem364075 A B b1 R a S' b P b0)). Qed.
Lemma lem364078 {A B : Type'} (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a0 : A) : term387 A B b0 b1 R a S' b P a0.
Proof. exact (@lem364077 A B b0 b1 R a S' b P a0). Qed.
Lemma lem364079 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : (term387 A B b0 b1 R a S' b P a0) = (term273 A B a0 b0 b1 R a S' b P).
Proof. exact (eq_refl (term387 A B b0 b1 R a S' b P a0)). Qed.
Lemma lem364080 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (EQ_MP (@lem364079 A B a0 b0 b1 R a S' b P) (@lem364078 A B b0 b1 R a S' b P a0)). Qed.
Lemma lem364082 {A B : Type'} (a0 : A) (b0 : B) (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) : term273 A B a0 b0 b1 R a S' b P.
Proof. exact (@lem362935 A B a0 b0 b1 R a S' b P (@lem364080 A B a0 b0 b1 R a S' b P)). Qed.
Lemma lem364083 {A B : Type'} (b1 : B) (R : type1402 A) (a : A) (S' : type1406 A B) (b : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term52 A B P a0 b0) : term287 A B b1 R a S' b P.
Proof. exact (@lem364082 A B a0 b0 b1 R a S' b P (@lem361969 A B P a0 b0 h1)). Qed.
Lemma lem364084 {A B : Type'} (b1 : B) (S' : type1406 A B) (b : B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a0 b0) : term284 A B b1 R a S' b P.
Proof. exact (@lem364083 A B b1 R a S' b P a0 b0 h2 (@lem362290 A B R a P h1)). Qed.
Lemma lem364085 {A B : Type'} (S' : type1406 A B) (b : B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) : term282 A B R a S' b P.
Proof. exact (@lem364084 A B b1 S' b R a P a0 b0 h1 h3 (@lem362293 A B P a b1 h2)). Qed.
Lemma lem364086 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term279 A B R a S' b P.
Proof. exact (@lem364085 A B S' b R a b1 P a0 b0 h1 h3 h4 (@lem362539 A B S' b P a h2)). Qed.
Lemma lem364087 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term271 A B R a S' b P.
Proof. exact (@lem364086 A B R S' b a b1 P a0 b0 h1 h2 h4 h5 (@lem362541 A B P a b h3)). Qed.
Lemma lem364088 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term272 A B R a S' b P) (h4 : term52 A B P a b) (h5 : term52 A B P a b1) (h6 : term52 A B P a0 b0) : False.
Proof. exact (@lem364087 A B R S' b a b1 P a0 b0 h1 h2 h4 h5 h6 (@lem362919 A B R a S' b P h3)). Qed.
Lemma lem364089 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term272 A B R a S' b P) (h4 : term52 A B P a b) (h5 : term52 A B P a b1) (h6 : term52 A B P a0 b0) : (term272 A B R a S' b P) = False.
Proof. exact (prop_ext (fun h7 : term272 A B R a S' b P => @lem364088 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem362919 A B R a S' b P h3)). Qed.
Lemma lem364090 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term272 A B R a S' b P) (h4 : term52 A B P a b) (h5 : term52 A B P a b1) (h6 : term52 A B P a0 b0) : False.
Proof. exact (EQ_MP (@lem364089 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5 h6) (@lem362919 A B R a S' b P h3)). Qed.
Lemma lem364091 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term271 A B R a S' b P.
Proof. exact (fun h0 : term272 A B R a S' b P => @lem364090 A B R S' b a b1 P a0 b0 h1 h2 h0 h3 h4 h5). Qed.
Lemma lem364092 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term269 A B R a S' b P.
Proof. exact (EQ_MP (@lem362918 A B R a S' b P) (@lem364091 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5)). Qed.
Lemma lem364093 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term155 A B R S' a b P.
Proof. exact (EQ_MP (@lem362914 A B R S' a b P) (@lem364092 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5)). Qed.
Lemma lem364094 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term156 A B R S' a b P.
Proof. exact (EQ_MP (@lem362626 A B R S' P a b h3) (@lem364093 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5)). Qed.
Lemma lem364095 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (ex_intro (term388 A B R S' P) (@pair A B a b) (@lem364094 A B R S' b a b1 P a0 b0 h1 h2 h3 h4 h5)). Qed.
Lemma lem364096 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term44 A B a b R S' P.
Proof. exact (fun h0 : term52 A B P a b => @lem364095 A B R S' b a b1 P a0 b0 h1 h2 h0 h3 h4). Qed.
Lemma lem364097 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term136 A B S' b P a) : term134 A B S' b P a.
Proof. exact (proj2 (@lem362538 A B S' b P a h1)). Qed.
Lemma lem364098 {A B : Type'} (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term136 A B S' b P a) : term52 A B P a b.
Proof. exact (proj1 (@lem362538 A B S' b P a h1)). Qed.
Lemma lem364099 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : (term134 A B S' b P a) = (term44 A B a b R S' P).
Proof. exact (prop_ext (fun h5 : term134 A B S' b P a => @lem364096 A B R S' b a b1 P a0 b0 h1 h2 h3 h4) (fun h5 : term44 A B a b R S' P => @lem362539 A B S' b P a h2)). Qed.
Lemma lem364100 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term44 A B a b R S' P.
Proof. exact (EQ_MP (@lem364099 A B R S' b a b1 P a0 b0 h1 h2 h3 h4) (@lem362539 A B S' b P a h2)). Qed.
Lemma lem364101 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (b : B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term134 A B S' b P a) (h3 : term52 A B P a b) (h4 : term52 A B P a b1) (h5 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364100 A B R S' b a b1 P a0 b0 h1 h2 h4 h5 (@lem362540 A B P a b h3)). Qed.
Lemma lem364102 {A B : Type'} (R : type1402 A) (b1 : B) (a0 : A) (b0 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P a b) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) (h5 : term136 A B S' b P a) : (term134 A B S' b P a) = (term32 A B R S' P).
Proof. exact (prop_ext (fun h6 : term134 A B S' b P a => @lem364101 A B R S' b a b1 P a0 b0 h1 h6 h2 h3 h4) (fun h6 : term32 A B R S' P => @lem364097 A B S' b P a h5)). Qed.
Lemma lem364103 {A B : Type'} (R : type1402 A) (b1 : B) (a0 : A) (b0 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P a b) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) (h5 : term136 A B S' b P a) : term32 A B R S' P.
Proof. exact (EQ_MP (@lem364102 A B R b1 a0 b0 S' b P a h1 h2 h3 h4 h5) (@lem364097 A B S' b P a h5)). Qed.
Lemma lem364104 {A B : Type'} (R : type1402 A) (b1 : B) (a0 : A) (b0 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) (h4 : term136 A B S' b P a) : (term52 A B P a b) = (term32 A B R S' P).
Proof. exact (prop_ext (fun h5 : term52 A B P a b => @lem364103 A B R b1 a0 b0 S' b P a h1 h5 h2 h3 h4) (fun h5 : term32 A B R S' P => @lem364098 A B S' b P a h4)). Qed.
Lemma lem364105 {A B : Type'} (R : type1402 A) (b1 : B) (a0 : A) (b0 : B) (S' : type1406 A B) (b : B) (P : type1210 A B) (a : A) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) (h4 : term136 A B S' b P a) : term32 A B R S' P.
Proof. exact (EQ_MP (@lem364104 A B R b1 a0 b0 S' b P a h1 h2 h3 h4) (@lem364098 A B S' b P a h4)). Qed.
Lemma lem364106 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term139 A B S' P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (ex_elim (@lem362537 A B S' P a h2) (fun b : B => fun h0 : term138 A B S' P a b => @lem364105 A B R b1 a0 b0 S' b P a h1 h3 h4 h0)). Qed.
Lemma lem364107 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) : term154 A B a R S' P.
Proof. exact (fun h0 : term139 A B S' P a => @lem364106 A B R S' a b1 P a0 b0 h1 h0 h2 h3). Qed.
Lemma lem364108 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) : term153 A B b1 a R S' P.
Proof. exact (EQ_MP (@lem362536 A B R S' P a b1 h2) (@lem364107 A B S' R a b1 P a0 b0 h1 h2 h3)). Qed.
Lemma lem364109 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term144 A B S' P a) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364108 A B S' R a b1 P a0 b0 h1 h3 h4 (@lem362448 A B b1 S' P a h2)). Qed.
Lemma lem364110 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) : term148 A B a R S' P.
Proof. exact (fun h0 : term144 A B S' P a => @lem364109 A B R S' a b1 P a0 b0 h1 h0 h2 h3). Qed.
Lemma lem364111 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term78 A B R a P) (h2 : term52 A B P a b1) (h3 : term52 A B P a0 b0) : term147 A B a R S' P.
Proof. exact (EQ_MP (@lem362444 A B a R S' P) (@lem364110 A B S' R a b1 P a0 b0 h1 h2 h3)). Qed.
Lemma lem364112 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (b1 : B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term52 A B P a b1) (h4 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364111 A B S' R a b1 P a0 b0 h2 h3 h4 (@lem362302 A B P a S' h1)). Qed.
Lemma lem364113 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term62 A B P a) (h4 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (ex_elim (@lem362292 A B P a h3) (fun b1 : B => fun h0 : term88 A B P a b1 => @lem364112 A B S' R a b1 P a0 b0 h1 h2 h0 h4)). Qed.
Lemma lem364114 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term52 A B P a0 b0) : term389 A B a R S' P.
Proof. exact (fun h0 : term62 A B P a => @lem364113 A B S' R a P a0 b0 h1 h2 h0 h3). Qed.
Lemma lem364115 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term80 A B R a P) : term78 A B R a P.
Proof. exact (proj2 (@lem362289 A B R a P h1)). Qed.
Lemma lem364116 {A B : Type'} (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term80 A B R a P) : term62 A B P a.
Proof. exact (proj1 (@lem362289 A B R a P h1)). Qed.
Lemma lem364117 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term52 A B P a0 b0) : (term78 A B R a P) = (term389 A B a R S' P).
Proof. exact (prop_ext (fun h4 : term78 A B R a P => @lem364114 A B S' R a P a0 b0 h1 h2 h3) (fun h4 : term389 A B a R S' P => @lem362290 A B R a P h2)). Qed.
Lemma lem364118 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term52 A B P a0 b0) : term389 A B a R S' P.
Proof. exact (EQ_MP (@lem364117 A B S' R a P a0 b0 h1 h2 h3) (@lem362290 A B R a P h2)). Qed.
Lemma lem364119 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (a : A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term78 A B R a P) (h3 : term62 A B P a) (h4 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364118 A B S' R a P a0 b0 h1 h2 h4 (@lem362291 A B P a h3)). Qed.
Lemma lem364120 {A B : Type'} (S' : type1406 A B) (a0 : A) (b0 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term17 A B S') (h2 : term62 A B P a) (h3 : term52 A B P a0 b0) (h4 : term80 A B R a P) : (term78 A B R a P) = (term32 A B R S' P).
Proof. exact (prop_ext (fun h5 : term78 A B R a P => @lem364119 A B S' R a P a0 b0 h1 h5 h2 h3) (fun h5 : term32 A B R S' P => @lem364115 A B R a P h4)). Qed.
Lemma lem364121 {A B : Type'} (S' : type1406 A B) (a0 : A) (b0 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term17 A B S') (h2 : term62 A B P a) (h3 : term52 A B P a0 b0) (h4 : term80 A B R a P) : term32 A B R S' P.
Proof. exact (EQ_MP (@lem364120 A B S' a0 b0 R a P h1 h2 h3 h4) (@lem364115 A B R a P h4)). Qed.
Lemma lem364122 {A B : Type'} (S' : type1406 A B) (a0 : A) (b0 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) (h3 : term80 A B R a P) : (term62 A B P a) = (term32 A B R S' P).
Proof. exact (prop_ext (fun h4 : term62 A B P a => @lem364121 A B S' a0 b0 R a P h1 h4 h2 h3) (fun h4 : term32 A B R S' P => @lem364116 A B R a P h3)). Qed.
Lemma lem364123 {A B : Type'} (S' : type1406 A B) (a0 : A) (b0 : B) (R : type1402 A) (a : A) (P : type1210 A B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) (h3 : term80 A B R a P) : term32 A B R S' P.
Proof. exact (EQ_MP (@lem364122 A B S' a0 b0 R a P h1 h2 h3) (@lem364116 A B R a P h3)). Qed.
Lemma lem364124 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term83 A B R P) (h3 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (ex_elim (@lem362288 A B R P h2) (fun a : A => fun h0 : term82 A B R P a => @lem364123 A B S' a0 b0 R a P h1 h3 h0)). Qed.
Lemma lem364125 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) : term115 A B R S' P.
Proof. exact (fun h0 : term83 A B R P => @lem364124 A B S' R P a0 b0 h1 h0 h2). Qed.
Lemma lem364126 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) : term114 A B a0 b0 R S' P.
Proof. exact (EQ_MP (@lem362287 A B R S' P a0 b0 h2) (@lem364125 A B R S' P a0 b0 h1 h2)). Qed.
Lemma lem364127 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term104 A B R P) (h2 : term17 A B S') (h3 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364126 A B R S' P a0 b0 h2 h3 (@lem362182 A B a0 b0 R P h1)). Qed.
Lemma lem364128 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) : term108 A B R S' P.
Proof. exact (fun h0 : term104 A B R P => @lem364127 A B R S' P a0 b0 h0 h1 h2). Qed.
Lemma lem364129 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term52 A B P a0 b0) : term107 A B R S' P.
Proof. exact (EQ_MP (@lem362175 A B R S' P) (@lem364128 A B R S' P a0 b0 h1 h2)). Qed.
Lemma lem364130 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (P : type1210 A B) (a0 : A) (b0 : B) (h1 : term17 A B S') (h2 : term9 A R) (h3 : term52 A B P a0 b0) : term32 A B R S' P.
Proof. exact (@lem364129 A B R S' P a0 b0 h1 h3 (@lem361972 A B P R h2)). Qed.
Lemma lem364131 {A B : Type'} (a0 : A) (b0 : B) (P : type1210 A B) (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term44 A B a0 b0 R S' P.
Proof. exact (fun h0 : term52 A B P a0 b0 => @lem364130 A B S' R P a0 b0 h1 h2 h0). Qed.
Lemma lem364136 {A B : Type'} (a0 : A) (P : type1210 A B) (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term48 A B a0 R S' P.
Proof. exact (fun b0 : B => @lem364131 A B a0 b0 P S' R h1 h2). Qed.
Lemma lem364141 {A B : Type'} (P : type1210 A B) (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term51 A B R S' P.
Proof. exact (fun a0 : A => @lem364136 A B a0 P S' R h1 h2). Qed.
Lemma lem364142 {A B : Type'} (P : type1210 A B) (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term31 A B R S' P.
Proof. exact (EQ_MP (@lem361968 A B R S' P) (@lem364141 A B P S' R h1 h2)). Qed.
Lemma lem364143 {A B : Type'} (P : type1210 A B) (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term30 A B R S' P.
Proof. exact (EQ_MP (@lem361948 A B R S' P) (@lem364142 A B P S' R h1 h2)). Qed.
Lemma lem364148 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term24 A B R S'.
Proof. exact (fun P : type1210 A B => @lem364143 A B P S' R h1 h2). Qed.
Lemma lem364149 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term19 A B R S') : term17 A B S'.
Proof. exact (proj2 (@lem361901 A B R S' h1)). Qed.
Lemma lem364150 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term19 A B R S') : term9 A R.
Proof. exact (proj1 (@lem361901 A B R S' h1)). Qed.
Lemma lem364151 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : (term17 A B S') = (term24 A B R S').
Proof. exact (prop_ext (fun h3 : term17 A B S' => @lem364148 A B S' R h1 h2) (fun h3 : term24 A B R S' => @lem361902 A B S' h1)). Qed.
Lemma lem364152 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term24 A B R S'.
Proof. exact (EQ_MP (@lem364151 A B S' R h1 h2) (@lem361902 A B S' h1)). Qed.
Lemma lem364153 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : (term9 A R) = (term24 A B R S').
Proof. exact (prop_ext (fun h3 : term9 A R => @lem364152 A B S' R h1 h2) (fun h3 : term24 A B R S' => @lem361903 A R h2)). Qed.
Lemma lem364154 {A B : Type'} (S' : type1406 A B) (R : type1402 A) (h1 : term17 A B S') (h2 : term9 A R) : term24 A B R S'.
Proof. exact (EQ_MP (@lem364153 A B S' R h1 h2) (@lem361903 A R h2)). Qed.
Lemma lem364155 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term9 A R) (h2 : term19 A B R S') : (term17 A B S') = (term24 A B R S').
Proof. exact (prop_ext (fun h3 : term17 A B S' => @lem364154 A B S' R h3 h1) (fun h3 : term24 A B R S' => @lem364149 A B R S' h2)). Qed.
Lemma lem364156 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term9 A R) (h2 : term19 A B R S') : term24 A B R S'.
Proof. exact (EQ_MP (@lem364155 A B R S' h1 h2) (@lem364149 A B R S' h2)). Qed.
Lemma lem364157 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term19 A B R S') : (term9 A R) = (term24 A B R S').
Proof. exact (prop_ext (fun h2 : term9 A R => @lem364156 A B R S' h2 h1) (fun h2 : term24 A B R S' => @lem364150 A B R S' h1)). Qed.
Lemma lem364158 {A B : Type'} (R : type1402 A) (S' : type1406 A B) (h1 : term19 A B R S') : term24 A B R S'.
Proof. exact (EQ_MP (@lem364157 A B R S' h1) (@lem364150 A B R S' h1)). Qed.
Lemma lem364159 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term27 A B R S'.
Proof. exact (fun h0 : term19 A B R S' => @lem364158 A B R S' h0). Qed.
Lemma lem364160 {A B : Type'} (R : type1402 A) (S' : type1406 A B) : term26 A B R S'.
Proof. exact (EQ_MP (@lem361900 A B R S') (@lem364159 A B R S')). Qed.
Lemma lem364165 {A B : Type'} (R : type1402 A) : term390 A B R.
Proof. exact (fun S' : type1406 A B => @lem364160 A B R S'). Qed.
Lemma lem364170 {A B : Type'} : term391 A B.
Proof. exact (fun R : type1402 A => @lem364165 A B R). Qed.
