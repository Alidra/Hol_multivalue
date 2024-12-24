Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_DIV_term_abbrevs.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_DIV_LMUL_spec.
Require Import REAL_EQ_LCANCEL_IMP_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import REAL_OF_NUM_MOD_spec.
Require Import REAL_SUB_LDISTRIB_spec.
Require Import REAL_SUB_REFL_spec.
Require Import TREAL_INV_0_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1340072_spec.
Require Import thm1340231_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Require Import thm940073_spec.
Lemma lem1669964 (m : nat) : term0 m.
Proof. exact (@lem1669963 m). Qed.
Lemma lem1669965 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1669966 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1669965 m) (@lem1669964 m)). Qed.
Lemma lem1669967 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1669966 m n). Qed.
Lemma lem1669968 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1669970 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1669971 (x : real) (h1 : term5) : term6 x.
Proof. exact (@lem1669970 h1 x). Qed.
Lemma lem1669972 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1669973 (x : real) (h1 : term5) : term7 x.
Proof. exact (EQ_MP (@lem1669972 x) (@lem1669971 x h1)). Qed.
Lemma lem1669974 (x : real) (y : real) (h1 : term5) : term8 x y.
Proof. exact (@lem1669973 x h1 y). Qed.
Lemma lem1669975 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1669976 (x : real) (y : real) (h1 : term5) : term9 x y.
Proof. exact (EQ_MP (@lem1669975 x y) (@lem1669974 x y h1)). Qed.
Lemma lem1669977 (x : real) (y : real) (z : real) (h1 : term5) : term10 x y z.
Proof. exact (@lem1669976 x y h1 z). Qed.
Lemma lem1669978 (z : real) (x : real) (y : real) : (term10 x y z) = (term11 z x y).
Proof. exact (eq_refl (term10 x y z)). Qed.
Lemma lem1669979 (z : real) (x : real) (y : real) (h1 : term5) : term11 z x y.
Proof. exact (EQ_MP (@lem1669978 z x y) (@lem1669977 x y z h1)). Qed.
Lemma lem1669980 (x : real) (z : real) (y : real) (h1 : term12 x z y) : term12 x z y.
Proof. exact (h1). Qed.
Lemma lem1669981 (x : real) (z : real) (y : real) (h1 : term5) (h2 : term12 x z y) : x = y.
Proof. exact (@lem1669979 z x y h1 (@lem1669980 x z y h2)). Qed.
Lemma lem1669982 (x : real) (z : real) (y : real) (h1 : term12 x z y) : term13 x y.
Proof. exact (fun h0 : term5 => @lem1669981 x z y h0 h1). Qed.
Lemma lem1669983 (x : real) (y : real) (h1 : term14 x y) : term14 x y.
Proof. exact (h1). Qed.
Lemma lem1669984 (x : real) (y : real) (h1 : term14 x y) : term13 x y.
Proof. exact (ex_elim (@lem1669983 x y h1) (fun z : real => fun h0 : term15 x y z => @lem1669982 x z y h0)). Qed.
Lemma lem1669985 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1669986 (x : real) (y : real) (h1 : term5) (h2 : term14 x y) : x = y.
Proof. exact (@lem1669984 x y h2 (@lem1669985 h1)). Qed.
Lemma lem1669987 (x : real) (y : real) (h1 : term5) : term16 x y.
Proof. exact (fun h0 : term14 x y => @lem1669986 x y h1 h0). Qed.
Lemma lem1669988 (x : real) (h1 : term5) : term17 x.
Proof. exact (fun y : real => @lem1669987 x y h1). Qed.
Lemma lem1669989 (h1 : term5) : term18.
Proof. exact (fun x : real => @lem1669988 x h1). Qed.
Lemma lem1669990 : term19.
Proof. exact (fun h0 : term5 => @lem1669989 h0). Qed.
Lemma lem1669991 : term18.
Proof. exact (@lem1669990 (@lem1640851)). Qed.
Lemma lem1669992 (x : real) : term20 x.
Proof. exact (@lem1669991 x). Qed.
Lemma lem1669993 (x : real) : (term20 x) = (term17 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1669994 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1669993 x) (@lem1669992 x)). Qed.
Lemma lem1669995 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1669994 x y). Qed.
Lemma lem1669996 (x : real) (y : real) : (term21 x y) = (term16 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1669998 (n : nat) : term22 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1669999 (n : nat) : (term22 n) = (term23 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1670000 (n : nat) : term23 n.
Proof. exact (EQ_MP (@lem1669999 n) (@lem1669998 n)). Qed.
Lemma lem1670002 (n : nat) (h1 : term24 n) : term24 n.
Proof. exact (h1). Qed.
Lemma lem1670003 (x : real) : term25 x.
Proof. exact (@lem1505261 x). Qed.
Lemma lem1670004 (x : real) : (term25 x) = ((real_sub x x) = term26).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1670006 (x : real) : term27 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1670007 (x : real) : (term27 x) = ((term28 x) = term26).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1670009 (x : real) : term29 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1670010 (x : real) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1670011 (x : real) : term30 x.
Proof. exact (EQ_MP (@lem1670010 x) (@lem1670009 x)). Qed.
Lemma lem1670012 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1670011 x y). Qed.
Lemma lem1670013 (x : real) (y : real) : (term31 x y) = ((real_div x y) = (term32 x y)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1670015 (n : nat) : term33 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem1670016 (n : nat) : (term33 n) = ((term34 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem1670021 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1670022 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem1670023 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term34 m).
Proof. exact (MK_COMB (@lem1670022 m) (@lem1670021 n h1)). Qed.
Lemma lem1670025 (n : nat) : (term34 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1670016 n) (@lem1670015 n)). Qed.
Lemma lem1670026 (m : nat) : (term34 m) = (NUMERAL 0).
Proof. exact (@lem1670025 m). Qed.
Lemma lem1670027 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1670023 m n h1) (@lem1670026 m)). Qed.
Lemma lem1670028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670029 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m n) = term26.
Proof. exact (MK_COMB (@lem1670028) (@lem1670027 m n h1)). Qed.
Lemma lem1670030 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1670031 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term36 m n) = term37.
Proof. exact (MK_COMB (@lem1670030) (@lem1670029 m n h1)). Qed.
Lemma lem1670035 (x : real) (y : real) : (real_div x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1670013 x y) (@lem1670012 x y)). Qed.
Lemma lem1670036 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (@lem1670035 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1670038 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1670039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670040 (n : nat) (h1 : n = (NUMERAL 0)) : (real_of_num n) = term26.
Proof. exact (MK_COMB (@lem1670039) (@lem1670038 n h1)). Qed.
Lemma lem1670041 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1670042 (n : nat) (h1 : n = (NUMERAL 0)) : (term40 n) = term41.
Proof. exact (MK_COMB (@lem1670041) (@lem1670040 n h1)). Qed.
Lemma lem1670044 : term41 = term26.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1670045 (n : nat) (h1 : n = (NUMERAL 0)) : (term40 n) = term26.
Proof. exact (TRANS (@lem1670042 n h1) (@lem1670044)). Qed.
Lemma lem1670046 (m : nat) : (term42 m) = (term42 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem1670047 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term39 m n) = (term43 m).
Proof. exact (MK_COMB (@lem1670046 m) (@lem1670045 n h1)). Qed.
Lemma lem1670049 (x : real) : (term28 x) = term26.
Proof. exact (EQ_MP (@lem1670007 x) (@lem1670006 x)). Qed.
Lemma lem1670050 (m : nat) : (term43 m) = term26.
Proof. exact (@lem1670049 (real_of_num m)). Qed.
Lemma lem1670051 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term39 m n) = term26.
Proof. exact (TRANS (@lem1670047 m n h1) (@lem1670050 m)). Qed.
Lemma lem1670052 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term38 m n) = term26.
Proof. exact (TRANS (@lem1670036 m n) (@lem1670051 m n h1)). Qed.
Lemma lem1670053 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1670054 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term44 m n) = term45.
Proof. exact (MK_COMB (@lem1670053) (@lem1670052 m n h1)). Qed.
Lemma lem1670056 (x : real) (y : real) : (real_div x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1670013 x y) (@lem1670012 x y)). Qed.
Lemma lem1670057 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (@lem1670056 (term3 m n) (real_of_num n)). Qed.
Lemma lem1670059 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1670060 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem1670061 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term48 m).
Proof. exact (MK_COMB (@lem1670060 m) (@lem1670059 n h1)). Qed.
Lemma lem1670062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670063 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term3 m n) = (term49 m).
Proof. exact (MK_COMB (@lem1670062) (@lem1670061 m n h1)). Qed.
Lemma lem1670064 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670065 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term50 m n) = (term51 m).
Proof. exact (MK_COMB (@lem1670064) (@lem1670063 m n h1)). Qed.
Lemma lem1670067 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1670068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670069 (n : nat) (h1 : n = (NUMERAL 0)) : (real_of_num n) = term26.
Proof. exact (MK_COMB (@lem1670068) (@lem1670067 n h1)). Qed.
Lemma lem1670070 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1670071 (n : nat) (h1 : n = (NUMERAL 0)) : (term40 n) = term41.
Proof. exact (MK_COMB (@lem1670070) (@lem1670069 n h1)). Qed.
Lemma lem1670073 : term41 = term26.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1670074 (n : nat) (h1 : n = (NUMERAL 0)) : (term40 n) = term26.
Proof. exact (TRANS (@lem1670071 n h1) (@lem1670073)). Qed.
Lemma lem1670075 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 m n) = (term52 m).
Proof. exact (MK_COMB (@lem1670065 m n h1) (@lem1670074 n h1)). Qed.
Lemma lem1670077 (x : real) : (term28 x) = term26.
Proof. exact (EQ_MP (@lem1670007 x) (@lem1670006 x)). Qed.
Lemma lem1670078 (m : nat) : (term52 m) = term26.
Proof. exact (@lem1670077 (term49 m)). Qed.
Lemma lem1670079 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 m n) = term26.
Proof. exact (TRANS (@lem1670075 m n h1) (@lem1670078 m)). Qed.
Lemma lem1670080 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term46 m n) = term26.
Proof. exact (TRANS (@lem1670057 m n) (@lem1670079 m n h1)). Qed.
Lemma lem1670081 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term53 m n) = term54.
Proof. exact (MK_COMB (@lem1670054 m n h1) (@lem1670080 m n h1)). Qed.
Lemma lem1670083 (x : real) : (real_sub x x) = term26.
Proof. exact (EQ_MP (@lem1670004 x) (@lem1670003 x)). Qed.
Lemma lem1670084 : term54 = term26.
Proof. exact (@lem1670083 term26). Qed.
Lemma lem1670085 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term53 m n) = term26.
Proof. exact (TRANS (@lem1670081 m n h1) (@lem1670084)). Qed.
Lemma lem1670086 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term35 m n) = (term53 m n)) = (term26 = term26).
Proof. exact (MK_COMB (@lem1670031 m n h1) (@lem1670085 m n h1)). Qed.
Lemma lem1670088 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1670089 (x : real) : (x = x) = True.
Proof. exact (@lem1670088 real x). Qed.
Lemma lem1670090 : (term26 = term26) = True.
Proof. exact (@lem1670089 term26). Qed.
Lemma lem1670091 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term35 m n) = (term53 m n)) = True.
Proof. exact (TRANS (@lem1670086 m n h1) (@lem1670090)). Qed.
Lemma lem1670092 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term35 m n) = (term53 m n)).
Proof. exact (SYM (@lem1670091 m n h1)). Qed.
Lemma lem1670093 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m n) = (term53 m n).
Proof. exact (EQ_MP (@lem1670092 m n h1) (@lem0)). Qed.
Lemma lem1670095 (x : real) (y : real) : term16 x y.
Proof. exact (EQ_MP (@lem1669996 x y) (@lem1669995 x y)). Qed.
Lemma lem1670096 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem1670095 (term35 m n) (term53 m n)). Qed.
Lemma lem1670097 (m : nat) : term56 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1670098 (m : nat) : (term56 m) = (term57 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem1670099 (m : nat) : term57 m.
Proof. exact (EQ_MP (@lem1670098 m) (@lem1670097 m)). Qed.
Lemma lem1670100 (m : nat) (n : nat) : term58 m n.
Proof. exact (@lem1670099 m n). Qed.
Lemma lem1670101 (m : nat) (n : nat) : (term58 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem1670103 (x : real) : term59 x.
Proof. exact (@lem1593226 x). Qed.
Lemma lem1670104 (x : real) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1670105 (x : real) : term60 x.
Proof. exact (EQ_MP (@lem1670104 x) (@lem1670103 x)). Qed.
Lemma lem1670106 (x : real) (y : real) : term61 x y.
Proof. exact (@lem1670105 x y). Qed.
Lemma lem1670107 (y : real) (x : real) : (term61 x y) = (term62 y x).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1670108 (y : real) (x : real) : term62 y x.
Proof. exact (EQ_MP (@lem1670107 y x) (@lem1670106 x y)). Qed.
Lemma lem1670109 (y : real) (h1 : term63 y) : term63 y.
Proof. exact (h1). Qed.
Lemma lem1670110 (x : real) (y : real) (h1 : term63 y) : (term64 x y) = x.
Proof. exact (@lem1670108 y x (@lem1670109 y h1)). Qed.
Lemma lem1670116 (x : real) : term65 x.
Proof. exact (@lem1526444 x). Qed.
Lemma lem1670117 (x : real) : (term65 x) = (term66 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1670118 (x : real) : term66 x.
Proof. exact (EQ_MP (@lem1670117 x) (@lem1670116 x)). Qed.
Lemma lem1670119 (x : real) (y : real) : term67 x y.
Proof. exact (@lem1670118 x y). Qed.
Lemma lem1670120 (y : real) (x : real) : (term67 x y) = (term68 y x).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1670121 (y : real) (x : real) : term68 y x.
Proof. exact (EQ_MP (@lem1670120 y x) (@lem1670119 x y)). Qed.
Lemma lem1670122 (y : real) (x : real) (z : real) : term69 y x z.
Proof. exact (@lem1670121 y x z). Qed.
Lemma lem1670123 (y : real) (x : real) (z : real) : (term69 y x z) = ((term70 x y z) = (term71 y x z)).
Proof. exact (eq_refl (term69 y x z)). Qed.
Lemma lem1670125 (n : nat) : term72 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1670141 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1670101 m n) (@lem1670100 m n)). Qed.
Lemma lem1670142 (n : nat) : ((real_of_num n) = term26) = (n = (NUMERAL 0)).
Proof. exact (@lem1670141 n (NUMERAL 0)). Qed.
Lemma lem1670144 (n : nat) (h1 : term24 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1670125 n (@lem1670002 n h1)). Qed.
Lemma lem1670145 (n : nat) (h1 : term24 n) : ((real_of_num n) = term26) = False.
Proof. exact (TRANS (@lem1670142 n) (@lem1670144 n h1)). Qed.
Lemma lem1670146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1670147 (n : nat) (h1 : term24 n) : (term73 n) = (~ False).
Proof. exact (MK_COMB (@lem1670146) (@lem1670145 n h1)). Qed.
Lemma lem1670149 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1670150 (n : nat) (h1 : term24 n) : (term73 n) = True.
Proof. exact (TRANS (@lem1670147 n h1) (@lem1670149)). Qed.
Lemma lem1670151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670152 (n : nat) (h1 : term24 n) : (term74 n) = (and True).
Proof. exact (MK_COMB (@lem1670151) (@lem1670150 n h1)). Qed.
Lemma lem1670156 (y : real) (x : real) (z : real) : (term70 x y z) = (term71 y x z).
Proof. exact (EQ_MP (@lem1670123 y x z) (@lem1670122 y x z)). Qed.
Lemma lem1670157 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (@lem1670156 (term38 m n) (real_of_num n) (term46 m n)). Qed.
Lemma lem1670159 (y : real) (x : real) : term62 y x.
Proof. exact (fun h0 : term63 y => @lem1670110 x y h0). Qed.
Lemma lem1670160 (n : nat) (m : nat) : term77 n m.
Proof. exact (@lem1670159 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1670162 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1670101 m n) (@lem1670100 m n)). Qed.
Lemma lem1670163 (n : nat) : ((real_of_num n) = term26) = (n = (NUMERAL 0)).
Proof. exact (@lem1670162 n (NUMERAL 0)). Qed.
Lemma lem1670165 (n : nat) (h1 : term24 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1670125 n (@lem1670002 n h1)). Qed.
Lemma lem1670166 (n : nat) (h1 : term24 n) : ((real_of_num n) = term26) = False.
Proof. exact (TRANS (@lem1670163 n) (@lem1670165 n h1)). Qed.
Lemma lem1670167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1670168 (n : nat) (h1 : term24 n) : (term73 n) = (~ False).
Proof. exact (MK_COMB (@lem1670167) (@lem1670166 n h1)). Qed.
Lemma lem1670170 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1670171 (n : nat) (h1 : term24 n) : (term73 n) = True.
Proof. exact (TRANS (@lem1670168 n h1) (@lem1670170)). Qed.
Lemma lem1670172 (n : nat) (h1 : term24 n) : True = (term73 n).
Proof. exact (SYM (@lem1670171 n h1)). Qed.
Lemma lem1670173 (n : nat) (h1 : term24 n) : term73 n.
Proof. exact (EQ_MP (@lem1670172 n h1) (@lem0)). Qed.
Lemma lem1670174 (m : nat) (n : nat) (h1 : term24 n) : (term78 m n) = (real_of_num m).
Proof. exact (@lem1670160 n m (@lem1670173 n h1)). Qed.
Lemma lem1670175 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1670176 (m : nat) (n : nat) (h1 : term24 n) : (term79 m n) = (term80 m).
Proof. exact (MK_COMB (@lem1670175) (@lem1670174 m n h1)). Qed.
Lemma lem1670178 (y : real) (x : real) : term62 y x.
Proof. exact (fun h0 : term63 y => @lem1670110 x y h0). Qed.
Lemma lem1670179 (m : nat) (n : nat) : term81 m n.
Proof. exact (@lem1670178 (real_of_num n) (term3 m n)). Qed.
Lemma lem1670181 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1670101 m n) (@lem1670100 m n)). Qed.
Lemma lem1670182 (n : nat) : ((real_of_num n) = term26) = (n = (NUMERAL 0)).
Proof. exact (@lem1670181 n (NUMERAL 0)). Qed.
Lemma lem1670184 (n : nat) (h1 : term24 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1670125 n (@lem1670002 n h1)). Qed.
Lemma lem1670185 (n : nat) (h1 : term24 n) : ((real_of_num n) = term26) = False.
Proof. exact (TRANS (@lem1670182 n) (@lem1670184 n h1)). Qed.
Lemma lem1670186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1670187 (n : nat) (h1 : term24 n) : (term73 n) = (~ False).
Proof. exact (MK_COMB (@lem1670186) (@lem1670185 n h1)). Qed.
Lemma lem1670189 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1670190 (n : nat) (h1 : term24 n) : (term73 n) = True.
Proof. exact (TRANS (@lem1670187 n h1) (@lem1670189)). Qed.
Lemma lem1670191 (n : nat) (h1 : term24 n) : True = (term73 n).
Proof. exact (SYM (@lem1670190 n h1)). Qed.
Lemma lem1670192 (n : nat) (h1 : term24 n) : term73 n.
Proof. exact (EQ_MP (@lem1670191 n h1) (@lem0)). Qed.
Lemma lem1670193 (m : nat) (n : nat) (h1 : term24 n) : (term82 m n) = (term3 m n).
Proof. exact (@lem1670179 m n (@lem1670192 n h1)). Qed.
Lemma lem1670194 (m : nat) (n : nat) (h1 : term24 n) : (term76 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem1670176 m n h1) (@lem1670193 m n h1)). Qed.
Lemma lem1670195 (m : nat) (n : nat) (h1 : term24 n) : (term75 m n) = (term83 m n).
Proof. exact (TRANS (@lem1670157 m n) (@lem1670194 m n h1)). Qed.
Lemma lem1670196 (m : nat) (n : nat) : (term84 m n) = (term84 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1670197 (m : nat) (n : nat) (h1 : term24 n) : ((term85 m n) = (term75 m n)) = ((term85 m n) = (term83 m n)).
Proof. exact (MK_COMB (@lem1670196 m n) (@lem1670195 m n h1)). Qed.
Lemma lem1670200 (m : nat) (n : nat) (h1 : term24 n) : (term86 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem1670152 n h1) (@lem1670197 m n h1)). Qed.
Lemma lem1670202 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1670203 (m : nat) (n : nat) : (term87 m n) = ((term85 m n) = (term83 m n)).
Proof. exact (@lem1670202 ((term85 m n) = (term83 m n))). Qed.
Lemma lem1670206 (m : nat) (n : nat) (h1 : term24 n) : (term86 m n) = ((term85 m n) = (term83 m n)).
Proof. exact (TRANS (@lem1670200 m n h1) (@lem1670203 m n)). Qed.
Lemma lem1670207 (m : nat) (n : nat) (h1 : term24 n) : ((term85 m n) = (term83 m n)) = (term86 m n).
Proof. exact (SYM (@lem1670206 m n h1)). Qed.
Lemma lem1670211 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1669968 m n) (@lem1669967 m n)). Qed.
Lemma lem1670212 (m : nat) : (term80 m) = (term80 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem1670213 (m : nat) (n : nat) : (term83 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem1670212 m) (@lem1670211 m n)). Qed.
Lemma lem1670214 (m : nat) (n : nat) : (term84 m n) = (term84 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1670215 (m : nat) (n : nat) : ((term85 m n) = (term83 m n)) = ((term85 m n) = (term88 m n)).
Proof. exact (MK_COMB (@lem1670214 m n) (@lem1670213 m n)). Qed.
Lemma lem1670218 (m : nat) (n : nat) : ((term85 m n) = (term88 m n)) = ((term85 m n) = (term83 m n)).
Proof. exact (SYM (@lem1670215 m n)). Qed.
Lemma lem1670228 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (@lem1483554 (term85 m n) (term88 m n)). Qed.
Lemma lem1670235 (m : nat) (n : nat) : (term91 m n) = (term85 m n).
Proof. exact (@lem1483474 (real_of_num n) (term35 m n)). Qed.
Lemma lem1670238 (m : nat) : (term80 m) = (term80 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem1670239 (m : nat) (n : nat) : (term4 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem1670238 m) (@lem1670235 m n)). Qed.
Lemma lem1670240 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (@lem1483519 (real_of_num m) (term85 m n)). Qed.
Lemma lem1670245 (n : nat) (m : nat) : (term93 m n) = (term94 n m).
Proof. exact (@lem1483488 (term95 m n) (real_of_num m)). Qed.
Lemma lem1670246 (n : nat) (m : nat) : (term92 m n) = (term94 n m).
Proof. exact (TRANS (@lem1670240 m n) (@lem1670245 n m)). Qed.
Lemma lem1670247 (n : nat) (m : nat) : (term4 m n) = (term94 n m).
Proof. exact (TRANS (@lem1670239 m n) (@lem1670246 n m)). Qed.
Lemma lem1670250 (m : nat) : (term80 m) = (term80 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem1670251 (n : nat) (m : nat) : (term88 m n) = (term96 n m).
Proof. exact (MK_COMB (@lem1670250 m) (@lem1670247 n m)). Qed.
Lemma lem1670252 (n : nat) (m : nat) : (term96 n m) = (term97 n m).
Proof. exact (@lem1483519 (real_of_num m) (term94 n m)). Qed.
Lemma lem1670253 (n : nat) (m : nat) : (term98 n m) = (term99 n m).
Proof. exact (@lem1483508 (term95 m n) term100 (real_of_num m)). Qed.
Lemma lem1670254 (m : nat) : (term101 m) = (term101 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem1670255 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (@lem1483476 term100 term100 (term85 m n)). Qed.
Lemma lem1670257 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1670258 : term106 = term107.
Proof. exact (@lem1670257 term108 term108). Qed.
Lemma lem1670259 : (term109 = (BIT1 0)) = (term110 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1670260 : term110 = term108.
Proof. exact (EQ_MP (@lem1670259) (@lem940073)). Qed.
Lemma lem1670261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670262 : term107 = term111.
Proof. exact (MK_COMB (@lem1670261) (@lem1670260)). Qed.
Lemma lem1670263 : term106 = term111.
Proof. exact (TRANS (@lem1670258) (@lem1670262)). Qed.
Lemma lem1670264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670265 : term112 = term113.
Proof. exact (MK_COMB (@lem1670264) (@lem1670263)). Qed.
Lemma lem1670266 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem1670267 (m : nat) (n : nat) : (term103 m n) = (term114 m n).
Proof. exact (MK_COMB (@lem1670265) (@lem1670266 m n)). Qed.
Lemma lem1670268 (m : nat) (n : nat) : (term102 m n) = (term114 m n).
Proof. exact (TRANS (@lem1670255 m n) (@lem1670267 m n)). Qed.
Lemma lem1670269 (m : nat) (n : nat) : (term114 m n) = (term85 m n).
Proof. exact (@lem1483436 (term85 m n)). Qed.
Lemma lem1670270 (m : nat) (n : nat) : (term102 m n) = (term85 m n).
Proof. exact (TRANS (@lem1670268 m n) (@lem1670269 m n)). Qed.
Lemma lem1670271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1670272 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (MK_COMB (@lem1670271) (@lem1670270 m n)). Qed.
Lemma lem1670273 (n : nat) (m : nat) : (term99 n m) = (term117 n m).
Proof. exact (MK_COMB (@lem1670272 m n) (@lem1670254 m)). Qed.
Lemma lem1670274 (n : nat) (m : nat) : (term98 n m) = (term117 n m).
Proof. exact (TRANS (@lem1670253 n m) (@lem1670273 n m)). Qed.
Lemma lem1670275 (m : nat) : (term118 m) = (term118 m).
Proof. exact (eq_refl (term118 m)). Qed.
Lemma lem1670276 (n : nat) (m : nat) : (term97 n m) = (term119 n m).
Proof. exact (MK_COMB (@lem1670275 m) (@lem1670274 n m)). Qed.
Lemma lem1670277 (n : nat) (m : nat) : (term119 n m) = (term120 n m).
Proof. exact (@lem1483484 (term85 m n) (real_of_num m) (term101 m)). Qed.
Lemma lem1670278 (m : nat) : (term121 m) = (term122 m).
Proof. exact (@lem1483442 term100 (real_of_num m)). Qed.
Lemma lem1670280 (m : nat) : (term123 m) = term26.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1670281 : term124 = term26.
Proof. exact (@lem1670280 term108). Qed.
Lemma lem1670282 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670283 : term125 = term126.
Proof. exact (MK_COMB (@lem1670282) (@lem1670281)). Qed.
Lemma lem1670284 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem1670285 (m : nat) : (term122 m) = (term127 m).
Proof. exact (MK_COMB (@lem1670283) (@lem1670284 m)). Qed.
Lemma lem1670286 (m : nat) : (term121 m) = (term127 m).
Proof. exact (TRANS (@lem1670278 m) (@lem1670285 m)). Qed.
Lemma lem1670287 (m : nat) : (term127 m) = term26.
Proof. exact (@lem1483446 (real_of_num m)). Qed.
Lemma lem1670288 (m : nat) : (term121 m) = term26.
Proof. exact (TRANS (@lem1670286 m) (@lem1670287 m)). Qed.
Lemma lem1670289 (m : nat) (n : nat) : (term116 m n) = (term116 m n).
Proof. exact (eq_refl (term116 m n)). Qed.
Lemma lem1670290 (m : nat) (n : nat) : (term120 n m) = (term128 m n).
Proof. exact (MK_COMB (@lem1670289 m n) (@lem1670288 m)). Qed.
Lemma lem1670291 (m : nat) (n : nat) : (term119 n m) = (term128 m n).
Proof. exact (TRANS (@lem1670277 n m) (@lem1670290 m n)). Qed.
Lemma lem1670292 (m : nat) (n : nat) : (term128 m n) = (term85 m n).
Proof. exact (@lem1483450 (term85 m n)). Qed.
Lemma lem1670293 (m : nat) (n : nat) : (term119 n m) = (term85 m n).
Proof. exact (TRANS (@lem1670291 m n) (@lem1670292 m n)). Qed.
Lemma lem1670294 (m : nat) (n : nat) : (term97 n m) = (term85 m n).
Proof. exact (TRANS (@lem1670276 n m) (@lem1670293 m n)). Qed.
Lemma lem1670295 (m : nat) (n : nat) : (term96 n m) = (term85 m n).
Proof. exact (TRANS (@lem1670252 n m) (@lem1670294 m n)). Qed.
Lemma lem1670296 (m : nat) (n : nat) : (term88 m n) = (term85 m n).
Proof. exact (TRANS (@lem1670251 n m) (@lem1670295 m n)). Qed.
Lemma lem1670305 (m : nat) (n : nat) : (term129 m n) = (term129 m n).
Proof. exact (eq_refl (term129 m n)). Qed.
Lemma lem1670306 (m : nat) (n : nat) : (term130 m n) = (term131 m n).
Proof. exact (MK_COMB (@lem1670305 m n) (@lem1670296 m n)). Qed.
Lemma lem1670307 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (@lem1483519 (term85 m n) (term85 m n)). Qed.
Lemma lem1670311 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (@lem1483442 term100 (term85 m n)). Qed.
Lemma lem1670313 (m : nat) : (term123 m) = term26.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1670314 : term124 = term26.
Proof. exact (@lem1670313 term108). Qed.
Lemma lem1670315 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670316 : term125 = term126.
Proof. exact (MK_COMB (@lem1670315) (@lem1670314)). Qed.
Lemma lem1670317 (m : nat) (n : nat) : (term85 m n) = (term85 m n).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem1670318 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (MK_COMB (@lem1670316) (@lem1670317 m n)). Qed.
Lemma lem1670319 (m : nat) (n : nat) : (term132 m n) = (term134 m n).
Proof. exact (TRANS (@lem1670311 m n) (@lem1670318 m n)). Qed.
Lemma lem1670320 (m : nat) (n : nat) : (term134 m n) = term26.
Proof. exact (@lem1483446 (term85 m n)). Qed.
Lemma lem1670322 (m : nat) (n : nat) : (term132 m n) = term26.
Proof. exact (TRANS (@lem1670319 m n) (@lem1670320 m n)). Qed.
Lemma lem1670323 (m : nat) (n : nat) : (term131 m n) = term26.
Proof. exact (TRANS (@lem1670307 m n) (@lem1670322 m n)). Qed.
Lemma lem1670324 (m : nat) (n : nat) : (term130 m n) = term26.
Proof. exact (TRANS (@lem1670306 m n) (@lem1670323 m n)). Qed.
Lemma lem1670325 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1670326 (m : nat) (n : nat) : (term135 m n) = term136.
Proof. exact (MK_COMB (@lem1670325) (@lem1670324 m n)). Qed.
Lemma lem1670327 : term136 = term137.
Proof. exact (@lem1483512 term26). Qed.
Lemma lem1670329 (x : nat) : (term138 x) = term26.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1670330 : term137 = term26.
Proof. exact (@lem1670329 term108). Qed.
Lemma lem1670331 : term136 = term26.
Proof. exact (TRANS (@lem1670327) (@lem1670330)). Qed.
Lemma lem1670332 (m : nat) (n : nat) : (term139 m n) = (term139 m n).
Proof. exact (eq_refl (term139 m n)). Qed.
Lemma lem1670333 (m : nat) (n : nat) : ((term135 m n) = term136) = ((term135 m n) = term26).
Proof. exact (MK_COMB (@lem1670332 m n) (@lem1670331)). Qed.
Lemma lem1670334 (m : nat) (n : nat) : (term135 m n) = term26.
Proof. exact (EQ_MP (@lem1670333 m n) (@lem1670326 m n)). Qed.
Lemma lem1670335 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1670336 (m : nat) (n : nat) : (term140 m n) = term141.
Proof. exact (MK_COMB (@lem1670335) (@lem1670334 m n)). Qed.
Lemma lem1670337 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem1670338 (m : nat) (n : nat) : (term142 m n) = term143.
Proof. exact (MK_COMB (@lem1670336 m n) (@lem1670337)). Qed.
Lemma lem1670339 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1670340 (m : nat) (n : nat) : (term144 m n) = term141.
Proof. exact (MK_COMB (@lem1670339) (@lem1670324 m n)). Qed.
Lemma lem1670341 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem1670342 (m : nat) (n : nat) : (term145 m n) = term143.
Proof. exact (MK_COMB (@lem1670340 m n) (@lem1670341)). Qed.
Lemma lem1670343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1670344 (m : nat) (n : nat) : (term146 m n) = term147.
Proof. exact (MK_COMB (@lem1670343) (@lem1670342 m n)). Qed.
Lemma lem1670345 (m : nat) (n : nat) : (term90 m n) = term148.
Proof. exact (MK_COMB (@lem1670344 m n) (@lem1670338 m n)). Qed.
Lemma lem1670359 (m : nat) (n : nat) : (term89 m n) = term148.
Proof. exact (TRANS (@lem1670228 m n) (@lem1670345 m n)). Qed.
Lemma lem1670369 (h1 : term148) : term148.
Proof. exact (h1). Qed.
Lemma lem1670370 (h1 : term143) : term143.
Proof. exact (h1). Qed.
Lemma lem1670372 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1670373 : term143 = term150.
Proof. exact (@lem1670372 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1670374 : term150 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1670375 : term143 = False.
Proof. exact (TRANS (@lem1670373) (@lem1670374)). Qed.
Lemma lem1670376 (h1 : term143) : False.
Proof. exact (EQ_MP (@lem1670375) (@lem1670370 h1)). Qed.
Lemma lem1670377 (h1 : term143) : term143.
Proof. exact (h1). Qed.
Lemma lem1670379 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1670380 : term143 = term150.
Proof. exact (@lem1670379 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1670381 : term150 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1670382 : term143 = False.
Proof. exact (TRANS (@lem1670380) (@lem1670381)). Qed.
Lemma lem1670383 (h1 : term143) : False.
Proof. exact (EQ_MP (@lem1670382) (@lem1670377 h1)). Qed.
Lemma lem1670384 (h1 : term148) : False.
Proof. exact (or_elim (@lem1670369 h1) (fun h0 : term143 => @lem1670376 h0) (fun h0 : term143 => @lem1670383 h0)). Qed.
Lemma lem1670386 (h1 : term148) : term148.
Proof. exact (h1). Qed.
Lemma lem1670387 (h1 : term148) : term148 = False.
Proof. exact (prop_ext (fun h2 : term148 => @lem1670384 h1) (fun h2 : False => @lem1670386 h1)). Qed.
Lemma lem1670388 (h1 : term148) : False.
Proof. exact (EQ_MP (@lem1670387 h1) (@lem1670386 h1)). Qed.
Lemma lem1670389 (m : nat) (n : nat) (h1 : term89 m n) : term89 m n.
Proof. exact (h1). Qed.
Lemma lem1670390 (m : nat) (n : nat) (h1 : term89 m n) : term148.
Proof. exact (EQ_MP (@lem1670359 m n) (@lem1670389 m n h1)). Qed.
Lemma lem1670391 (m : nat) (n : nat) (h1 : term89 m n) : term148 = False.
Proof. exact (prop_ext (fun h2 : term148 => @lem1670388 h2) (fun h2 : False => @lem1670390 m n h1)). Qed.
Lemma lem1670392 (m : nat) (n : nat) (h1 : term89 m n) : False.
Proof. exact (EQ_MP (@lem1670391 m n h1) (@lem1670390 m n h1)). Qed.
Lemma lem1670393 (m : nat) (n : nat) : term151 m n.
Proof. exact (fun h0 : term89 m n => @lem1670392 m n h0). Qed.
Lemma lem1670394 (m : nat) (n : nat) : term152 m n.
Proof. exact (@lem1386578 ((term85 m n) = (term88 m n))). Qed.
Lemma lem1670395 (m : nat) (n : nat) : (term85 m n) = (term88 m n).
Proof. exact (@lem1670394 m n (@lem1670393 m n)). Qed.
Lemma lem1670396 (m : nat) (n : nat) : (term85 m n) = (term83 m n).
Proof. exact (EQ_MP (@lem1670218 m n) (@lem1670395 m n)). Qed.
Lemma lem1670397 (m : nat) (n : nat) (h1 : term24 n) : term86 m n.
Proof. exact (EQ_MP (@lem1670207 m n h1) (@lem1670396 m n)). Qed.
Lemma lem1670398 (m : nat) (n : nat) (h1 : term24 n) : term153 m n.
Proof. exact (ex_intro (term154 m n) (real_of_num n) (@lem1670397 m n h1)). Qed.
Lemma lem1670399 (m : nat) (n : nat) (h1 : term24 n) : (term35 m n) = (term53 m n).
Proof. exact (@lem1670096 m n (@lem1670398 m n h1)). Qed.
Lemma lem1670400 (m : nat) (n : nat) : (term35 m n) = (term53 m n).
Proof. exact (or_elim (@lem1670000 n) (fun h0 : n = (NUMERAL 0) => @lem1670093 m n h0) (fun h0 : term24 n => @lem1670399 m n h0)). Qed.
Lemma lem1670405 (m : nat) : term155 m.
Proof. exact (fun n : nat => @lem1670400 m n). Qed.
Lemma lem1670410 : term156.
Proof. exact (fun m : nat => @lem1670405 m). Qed.
