Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1321091_term_abbrevs.
Require Import NADD_LDISTRIB_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320949 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320950 (y : nadd) (x : nadd) (z : nadd) : (term1 y x z) = ((term2 x y z) = (term3 y x z)).
Proof. exact (@lem1320949 (term4 x y z) (term5 y x z)). Qed.
Lemma lem1320954 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320955 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1320954 x (nadd_add y z)). Qed.
Lemma lem1320957 (x : nadd) (y : nadd) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320958 (y : nadd) (z : nadd) : (term9 y z) = (term10 y z).
Proof. exact (@lem1320957 y z). Qed.
Lemma lem1320959 (x : nadd) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1320960 (x : nadd) (y : nadd) (z : nadd) : (term8 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1320959 x) (@lem1320958 y z)). Qed.
Lemma lem1320961 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem1320955 x y z) (@lem1320960 x y z)). Qed.
Lemma lem1320962 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320963 (x : nadd) (y : nadd) (z : nadd) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem1320962) (@lem1320961 x y z)). Qed.
Lemma lem1320965 (x : nadd) (y : nadd) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320966 (y : nadd) (x : nadd) (z : nadd) : (term3 y x z) = (term15 y x z).
Proof. exact (@lem1320965 (nadd_mul x y) (nadd_mul x z)). Qed.
Lemma lem1320968 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320969 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1320970 (x : nadd) (y : nadd) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1320969) (@lem1320968 x y)). Qed.
Lemma lem1320972 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320973 (x : nadd) (z : nadd) : (term6 x z) = (term7 x z).
Proof. exact (@lem1320972 x z). Qed.
Lemma lem1320974 (y : nadd) (x : nadd) (z : nadd) : (term15 y x z) = (term18 y x z).
Proof. exact (MK_COMB (@lem1320970 x y) (@lem1320973 x z)). Qed.
Lemma lem1320975 (y : nadd) (x : nadd) (z : nadd) : (term3 y x z) = (term18 y x z).
Proof. exact (TRANS (@lem1320966 y x z) (@lem1320974 y x z)). Qed.
Lemma lem1320976 (y : nadd) (x : nadd) (z : nadd) : ((term2 x y z) = (term3 y x z)) = ((term12 x y z) = (term18 y x z)).
Proof. exact (MK_COMB (@lem1320963 x y z) (@lem1320975 y x z)). Qed.
Lemma lem1320979 (y : nadd) (x : nadd) (z : nadd) : (term1 y x z) = ((term12 x y z) = (term18 y x z)).
Proof. exact (TRANS (@lem1320950 y x z) (@lem1320976 y x z)). Qed.
Lemma lem1320980 (y : nadd) (x : nadd) : (term19 y x) = (term20 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1320979 y x z)). Qed.
Lemma lem1320981 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320982 (y : nadd) (x : nadd) : (term21 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1320981) (@lem1320980 y x)). Qed.
Lemma lem1320988 (P : hreal -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320989 (y : nadd) (x : nadd) : (term25 y x) = (term26 y x).
Proof. exact (@lem1320988 (term27 y x)). Qed.
Lemma lem1320990 (y : nadd) (x : nadd) (z : nadd) : (term28 y x z) = ((term12 x y z) = (term18 y x z)).
Proof. exact (eq_refl (term28 y x z)). Qed.
Lemma lem1320991 (y : nadd) (x : nadd) : (term29 y x) = (term20 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1320990 y x z)). Qed.
Lemma lem1320992 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320993 (y : nadd) (x : nadd) : (term25 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1320992) (@lem1320991 y x)). Qed.
Lemma lem1320994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320995 (y : nadd) (x : nadd) : (term30 y x) = (term31 y x).
Proof. exact (MK_COMB (@lem1320994) (@lem1320993 y x)). Qed.
Lemma lem1320996 (y : nadd) (x : nadd) (z : hreal) : (term32 y x z) = ((term33 x y z) = (term34 y x z)).
Proof. exact (eq_refl (term32 y x z)). Qed.
Lemma lem1320997 (y : nadd) (x : nadd) : (term35 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : hreal => @lem1320996 y x z)). Qed.
Lemma lem1320998 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320999 (y : nadd) (x : nadd) : (term26 y x) = (term36 y x).
Proof. exact (MK_COMB (@lem1320998) (@lem1320997 y x)). Qed.
Lemma lem1321000 (y : nadd) (x : nadd) : ((term25 y x) = (term26 y x)) = ((term22 y x) = (term36 y x)).
Proof. exact (MK_COMB (@lem1320995 y x) (@lem1320999 y x)). Qed.
Lemma lem1321001 (y : nadd) (x : nadd) : (term22 y x) = (term36 y x).
Proof. exact (EQ_MP (@lem1321000 y x) (@lem1320989 y x)). Qed.
Lemma lem1321010 (y : nadd) (x : nadd) : (term21 y x) = (term36 y x).
Proof. exact (TRANS (@lem1320982 y x) (@lem1321001 y x)). Qed.
Lemma lem1321011 (x : nadd) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1321010 y x)). Qed.
Lemma lem1321012 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321013 (x : nadd) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1321012) (@lem1321011 x)). Qed.
Lemma lem1321019 (P : hreal -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1321020 (x : nadd) : (term41 x) = (term42 x).
Proof. exact (@lem1321019 (term43 x)). Qed.
Lemma lem1321021 (y : nadd) (x : nadd) : (term44 x y) = (term36 y x).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1321022 (x : nadd) : (term45 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1321021 y x)). Qed.
Lemma lem1321023 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321024 (x : nadd) : (term41 x) = (term40 x).
Proof. exact (MK_COMB (@lem1321023) (@lem1321022 x)). Qed.
Lemma lem1321025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321026 (x : nadd) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1321025) (@lem1321024 x)). Qed.
Lemma lem1321027 (y : hreal) (x : nadd) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1321028 (x : nadd) : (term50 x) = (term43 x).
Proof. exact (fun_ext (fun y : hreal => @lem1321027 y x)). Qed.
Lemma lem1321029 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321030 (x : nadd) : (term42 x) = (term51 x).
Proof. exact (MK_COMB (@lem1321029) (@lem1321028 x)). Qed.
Lemma lem1321031 (x : nadd) : ((term41 x) = (term42 x)) = ((term40 x) = (term51 x)).
Proof. exact (MK_COMB (@lem1321026 x) (@lem1321030 x)). Qed.
Lemma lem1321032 (x : nadd) : (term40 x) = (term51 x).
Proof. exact (EQ_MP (@lem1321031 x) (@lem1321020 x)). Qed.
Lemma lem1321047 (x : nadd) : (term39 x) = (term51 x).
Proof. exact (TRANS (@lem1321013 x) (@lem1321032 x)). Qed.
Lemma lem1321048 : term52 = term53.
Proof. exact (fun_ext (fun x : nadd => @lem1321047 x)). Qed.
Lemma lem1321049 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321050 : term54 = term55.
Proof. exact (MK_COMB (@lem1321049) (@lem1321048)). Qed.
Lemma lem1321056 (P : hreal -> Prop) : (term23 P) = (term24 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1321057 : term56 = term57.
Proof. exact (@lem1321056 term58). Qed.
Lemma lem1321058 (x : nadd) : (term59 x) = (term51 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1321059 : term60 = term53.
Proof. exact (fun_ext (fun x : nadd => @lem1321058 x)). Qed.
Lemma lem1321060 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321061 : term56 = term55.
Proof. exact (MK_COMB (@lem1321060) (@lem1321059)). Qed.
Lemma lem1321062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321063 : term61 = term62.
Proof. exact (MK_COMB (@lem1321062) (@lem1321061)). Qed.
Lemma lem1321064 (x : hreal) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1321065 : term65 = term58.
Proof. exact (fun_ext (fun x : hreal => @lem1321064 x)). Qed.
Lemma lem1321066 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321067 : term57 = term66.
Proof. exact (MK_COMB (@lem1321066) (@lem1321065)). Qed.
Lemma lem1321068 : (term56 = term57) = (term55 = term66).
Proof. exact (MK_COMB (@lem1321063) (@lem1321067)). Qed.
Lemma lem1321069 : term55 = term66.
Proof. exact (EQ_MP (@lem1321068) (@lem1321057)). Qed.
Lemma lem1321090 : term54 = term66.
Proof. exact (TRANS (@lem1321050) (@lem1321069)). Qed.
Lemma lem1321091 : term66.
Proof. exact (EQ_MP (@lem1321090) (@lem1278840)). Qed.
