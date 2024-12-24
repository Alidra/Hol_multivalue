Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_MUL_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_MUL_AC_spec.
Require Import REAL_MUL_LINV_UNIQ_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import REFL_CLAUSE_spec.
Require Import TREAL_INV_0_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1340072_spec.
Require Import thm1340174_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1594901 (x : real) : term0 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1594902 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1594904 (x : real) : term2 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1594905 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1594907 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1594908 {A : Type'} (x : A) : (term4 A x) = ((x = x) = True).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem1594910 (n : real) (m : real) (p : real) : term5 n m p.
Proof. exact (proj2 (@lem1486340 n m p)). Qed.
Lemma lem1594917 (m : real) (n : real) (p : real) : (term6 m n p) = (term7 m n p).
Proof. exact (proj1 (@lem1594910 n m p)). Qed.
Lemma lem1594918 (a : real) (b : real) (c : real) (d : real) : (term8 a b c d) = (term9 a b c d).
Proof. exact (@lem1594917 a b (real_mul c d)). Qed.
Lemma lem1594934 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594935 (a : real) (b : real) (c : real) (d : real) : (term10 a b c d) = (term11 a b c d).
Proof. exact (MK_COMB (@lem1594934) (@lem1594918 a b c d)). Qed.
Lemma lem1594937 (m : real) (n : real) (p : real) : (term6 m n p) = (term7 m n p).
Proof. exact (proj1 (@lem1594910 n m p)). Qed.
Lemma lem1594938 (a : real) (c : real) (b : real) (d : real) : (term8 a c b d) = (term9 a c b d).
Proof. exact (@lem1594937 a c (real_mul b d)). Qed.
Lemma lem1594946 (n : real) (m : real) (p : real) : (term7 m n p) = (term7 n m p).
Proof. exact (proj2 (@lem1594910 n m p)). Qed.
Lemma lem1594947 (b : real) (c : real) (d : real) : (term7 c b d) = (term7 b c d).
Proof. exact (@lem1594946 b c d). Qed.
Lemma lem1594957 (a : real) : (real_mul a) = (real_mul a).
Proof. exact (eq_refl (real_mul a)). Qed.
Lemma lem1594958 (a : real) (b : real) (c : real) (d : real) : (term9 a c b d) = (term9 a b c d).
Proof. exact (MK_COMB (@lem1594957 a) (@lem1594947 b c d)). Qed.
Lemma lem1594965 (a : real) (b : real) (c : real) (d : real) : (term8 a c b d) = (term9 a b c d).
Proof. exact (TRANS (@lem1594938 a c b d) (@lem1594958 a b c d)). Qed.
Lemma lem1594966 (a : real) (b : real) (c : real) (d : real) : ((term8 a b c d) = (term8 a c b d)) = ((term9 a b c d) = (term9 a b c d)).
Proof. exact (MK_COMB (@lem1594935 a b c d) (@lem1594965 a b c d)). Qed.
Lemma lem1594968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1594908 A x) (@lem1594907 A x)). Qed.
Lemma lem1594969 (x : real) : (x = x) = True.
Proof. exact (@lem1594968 real x). Qed.
Lemma lem1594970 (a : real) (b : real) (c : real) (d : real) : ((term9 a b c d) = (term9 a b c d)) = True.
Proof. exact (@lem1594969 (term9 a b c d)). Qed.
Lemma lem1594971 (a : real) (c : real) (b : real) (d : real) : ((term8 a b c d) = (term8 a c b d)) = True.
Proof. exact (TRANS (@lem1594966 a b c d) (@lem1594970 a b c d)). Qed.
Lemma lem1594972 (a : real) (c : real) (b : real) (d : real) : True = ((term8 a b c d) = (term8 a c b d)).
Proof. exact (SYM (@lem1594971 a c b d)). Qed.
Lemma lem1594974 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1594975 (x : real) (h1 : term12) : term13 x.
Proof. exact (@lem1594974 h1 x). Qed.
Lemma lem1594976 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1594977 (x : real) (h1 : term12) : term14 x.
Proof. exact (EQ_MP (@lem1594976 x) (@lem1594975 x h1)). Qed.
Lemma lem1594978 (x : real) (y : real) (h1 : term12) : term15 x y.
Proof. exact (@lem1594977 x h1 y). Qed.
Lemma lem1594979 (y : real) (x : real) : (term15 x y) = (term16 y x).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1594980 (y : real) (x : real) (h1 : term12) : term16 y x.
Proof. exact (EQ_MP (@lem1594979 y x) (@lem1594978 x y h1)). Qed.
Lemma lem1594981 (x : real) (y : real) (h1 : (real_mul x y) = term17) : (real_mul x y) = term17.
Proof. exact (h1). Qed.
Lemma lem1594982 (x : real) (y : real) (h1 : term12) (h2 : (real_mul x y) = term17) : (real_inv y) = x.
Proof. exact (@lem1594980 y x h1 (@lem1594981 x y h2)). Qed.
Lemma lem1594983 (x : real) (y : real) (h1 : (real_mul x y) = term17) : term18 y x.
Proof. exact (fun h0 : term12 => @lem1594982 x y h0 h1). Qed.
Lemma lem1594984 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1594985 (x : real) (y : real) (h1 : term12) (h2 : (real_mul x y) = term17) : (real_inv y) = x.
Proof. exact (@lem1594983 x y h2 (@lem1594984 h1)). Qed.
Lemma lem1594986 (y : real) (x : real) (h1 : term12) : term16 y x.
Proof. exact (fun h0 : (real_mul x y) = term17 => @lem1594985 x y h1 h0). Qed.
Lemma lem1594987 (y : real) (h1 : term12) : term19 y.
Proof. exact (fun x : real => @lem1594986 y x h1). Qed.
Lemma lem1594988 (h1 : term12) : term20.
Proof. exact (fun y : real => @lem1594987 y h1). Qed.
Lemma lem1594989 : term21.
Proof. exact (fun h0 : term12 => @lem1594988 h0). Qed.
Lemma lem1594990 : term20.
Proof. exact (@lem1594989 (@lem1587738)). Qed.
Lemma lem1594991 (y : real) : term22 y.
Proof. exact (@lem1594990 y). Qed.
Lemma lem1594992 (y : real) : (term22 y) = (term19 y).
Proof. exact (eq_refl (term22 y)). Qed.
Lemma lem1594993 (y : real) : term19 y.
Proof. exact (EQ_MP (@lem1594992 y) (@lem1594991 y)). Qed.
Lemma lem1594994 (y : real) (x : real) : term23 y x.
Proof. exact (@lem1594993 y x). Qed.
Lemma lem1594995 (y : real) (x : real) : (term23 y x) = (term16 y x).
Proof. exact (eq_refl (term23 y x)). Qed.
Lemma lem1594997 (x : real) : term24 x.
Proof. exact (@lem9784 (x = term25)). Qed.
Lemma lem1594998 (x : real) : (term24 x) = (term26 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1594999 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1594998 x) (@lem1594997 x)). Qed.
Lemma lem1595001 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1595002 (y : real) : term24 y.
Proof. exact (@lem9784 (y = term25)). Qed.
Lemma lem1595003 (y : real) : (term24 y) = (term26 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem1595004 (y : real) : term26 y.
Proof. exact (EQ_MP (@lem1595003 y) (@lem1595002 y)). Qed.
Lemma lem1595006 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1595010 (x : real) : term28 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1595011 (x : real) : (term28 x) = ((term29 x) = term25).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1595016 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1595017 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595018 (x : real) (h1 : x = term25) : (real_mul x) = term30.
Proof. exact (MK_COMB (@lem1595017) (@lem1595016 x h1)). Qed.
Lemma lem1595020 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1595021 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (real_mul x y) = term31.
Proof. exact (MK_COMB (@lem1595018 x h1) (@lem1595020 y h2)). Qed.
Lemma lem1595023 (x : real) : (term29 x) = term25.
Proof. exact (EQ_MP (@lem1595011 x) (@lem1595010 x)). Qed.
Lemma lem1595024 : term31 = term25.
Proof. exact (@lem1595023 term25). Qed.
Lemma lem1595025 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (real_mul x y) = term25.
Proof. exact (TRANS (@lem1595021 x y h1 h2) (@lem1595024)). Qed.
Lemma lem1595026 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595027 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term32 x y) = term33.
Proof. exact (MK_COMB (@lem1595026) (@lem1595025 x y h1 h2)). Qed.
Lemma lem1595029 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595030 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term32 x y) = term25.
Proof. exact (TRANS (@lem1595027 x y h1 h2) (@lem1595029)). Qed.
Lemma lem1595031 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595032 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1595031) (@lem1595030 x y h1 h2)). Qed.
Lemma lem1595034 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1595035 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595036 (x : real) (h1 : x = term25) : (real_inv x) = term33.
Proof. exact (MK_COMB (@lem1595035) (@lem1595034 x h1)). Qed.
Lemma lem1595038 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595039 (x : real) (h1 : x = term25) : (real_inv x) = term25.
Proof. exact (TRANS (@lem1595036 x h1) (@lem1595038)). Qed.
Lemma lem1595040 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595041 (x : real) (h1 : x = term25) : (term36 x) = term30.
Proof. exact (MK_COMB (@lem1595040) (@lem1595039 x h1)). Qed.
Lemma lem1595043 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1595044 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595045 (y : real) (h1 : y = term25) : (real_inv y) = term33.
Proof. exact (MK_COMB (@lem1595044) (@lem1595043 y h1)). Qed.
Lemma lem1595047 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595048 (y : real) (h1 : y = term25) : (real_inv y) = term25.
Proof. exact (TRANS (@lem1595045 y h1) (@lem1595047)). Qed.
Lemma lem1595049 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term37 x y) = term31.
Proof. exact (MK_COMB (@lem1595041 x h1) (@lem1595048 y h2)). Qed.
Lemma lem1595051 (x : real) : (term29 x) = term25.
Proof. exact (EQ_MP (@lem1595011 x) (@lem1595010 x)). Qed.
Lemma lem1595052 : term31 = term25.
Proof. exact (@lem1595051 term25). Qed.
Lemma lem1595053 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term37 x y) = term25.
Proof. exact (TRANS (@lem1595049 x y h1 h2) (@lem1595052)). Qed.
Lemma lem1595054 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : ((term32 x y) = (term37 x y)) = (term25 = term25).
Proof. exact (MK_COMB (@lem1595032 x y h1 h2) (@lem1595053 x y h1 h2)). Qed.
Lemma lem1595056 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595057 (x : real) : (x = x) = True.
Proof. exact (@lem1595056 real x). Qed.
Lemma lem1595058 : (term25 = term25) = True.
Proof. exact (@lem1595057 term25). Qed.
Lemma lem1595059 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : ((term32 x y) = (term37 x y)) = True.
Proof. exact (TRANS (@lem1595054 x y h1 h2) (@lem1595058)). Qed.
Lemma lem1595060 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : True = ((term32 x y) = (term37 x y)).
Proof. exact (SYM (@lem1595059 x y h1 h2)). Qed.
Lemma lem1595061 (x : real) (y : real) (h1 : x = term25) (h2 : y = term25) : (term32 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem1595060 x y h1 h2) (@lem0)). Qed.
Lemma lem1595065 (x : real) : term28 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1595066 (x : real) : (term28 x) = ((term29 x) = term25).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1595084 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1595085 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595086 (x : real) (h1 : x = term25) : (real_mul x) = term30.
Proof. exact (MK_COMB (@lem1595085) (@lem1595084 x h1)). Qed.
Lemma lem1595087 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1595088 (y : real) (x : real) (h1 : x = term25) : (real_mul x y) = (term29 y).
Proof. exact (MK_COMB (@lem1595086 x h1) (@lem1595087 y)). Qed.
Lemma lem1595090 (x : real) : (term29 x) = term25.
Proof. exact (EQ_MP (@lem1595066 x) (@lem1595065 x)). Qed.
Lemma lem1595091 (y : real) : (term29 y) = term25.
Proof. exact (@lem1595090 y). Qed.
Lemma lem1595092 (y : real) (x : real) (h1 : x = term25) : (real_mul x y) = term25.
Proof. exact (TRANS (@lem1595088 y x h1) (@lem1595091 y)). Qed.
Lemma lem1595093 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595094 (y : real) (x : real) (h1 : x = term25) : (term32 x y) = term33.
Proof. exact (MK_COMB (@lem1595093) (@lem1595092 y x h1)). Qed.
Lemma lem1595096 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595097 (y : real) (x : real) (h1 : x = term25) : (term32 x y) = term25.
Proof. exact (TRANS (@lem1595094 y x h1) (@lem1595096)). Qed.
Lemma lem1595098 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595099 (y : real) (x : real) (h1 : x = term25) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1595098) (@lem1595097 y x h1)). Qed.
Lemma lem1595101 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1595102 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595103 (x : real) (h1 : x = term25) : (real_inv x) = term33.
Proof. exact (MK_COMB (@lem1595102) (@lem1595101 x h1)). Qed.
Lemma lem1595105 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595106 (x : real) (h1 : x = term25) : (real_inv x) = term25.
Proof. exact (TRANS (@lem1595103 x h1) (@lem1595105)). Qed.
Lemma lem1595107 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1595108 (x : real) (h1 : x = term25) : (term36 x) = term30.
Proof. exact (MK_COMB (@lem1595107) (@lem1595106 x h1)). Qed.
Lemma lem1595109 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1595110 (y : real) (x : real) (h1 : x = term25) : (term37 x y) = (term38 y).
Proof. exact (MK_COMB (@lem1595108 x h1) (@lem1595109 y)). Qed.
Lemma lem1595112 (x : real) : (term29 x) = term25.
Proof. exact (EQ_MP (@lem1595066 x) (@lem1595065 x)). Qed.
Lemma lem1595113 (y : real) : (term38 y) = term25.
Proof. exact (@lem1595112 (real_inv y)). Qed.
Lemma lem1595114 (y : real) (x : real) (h1 : x = term25) : (term37 x y) = term25.
Proof. exact (TRANS (@lem1595110 y x h1) (@lem1595113 y)). Qed.
Lemma lem1595115 (y : real) (x : real) (h1 : x = term25) : ((term32 x y) = (term37 x y)) = (term25 = term25).
Proof. exact (MK_COMB (@lem1595099 y x h1) (@lem1595114 y x h1)). Qed.
Lemma lem1595117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595118 (x : real) : (x = x) = True.
Proof. exact (@lem1595117 real x). Qed.
Lemma lem1595119 : (term25 = term25) = True.
Proof. exact (@lem1595118 term25). Qed.
Lemma lem1595120 (y : real) (x : real) (h1 : x = term25) : ((term32 x y) = (term37 x y)) = True.
Proof. exact (TRANS (@lem1595115 y x h1) (@lem1595119)). Qed.
Lemma lem1595121 (y : real) (x : real) (h1 : x = term25) : True = ((term32 x y) = (term37 x y)).
Proof. exact (SYM (@lem1595120 y x h1)). Qed.
Lemma lem1595122 (y : real) (x : real) (h1 : x = term25) : (term32 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem1595121 y x h1) (@lem0)). Qed.
Lemma lem1595123 (x : real) : term39 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1595124 (x : real) : (term39 x) = ((term40 x) = term25).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1595145 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1595146 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1595147 (x : real) (y : real) (h1 : y = term25) : (real_mul x y) = (term40 x).
Proof. exact (MK_COMB (@lem1595146 x) (@lem1595145 y h1)). Qed.
Lemma lem1595149 (x : real) : (term40 x) = term25.
Proof. exact (EQ_MP (@lem1595124 x) (@lem1595123 x)). Qed.
Lemma lem1595150 (x : real) (y : real) (h1 : y = term25) : (real_mul x y) = term25.
Proof. exact (TRANS (@lem1595147 x y h1) (@lem1595149 x)). Qed.
Lemma lem1595151 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595152 (x : real) (y : real) (h1 : y = term25) : (term32 x y) = term33.
Proof. exact (MK_COMB (@lem1595151) (@lem1595150 x y h1)). Qed.
Lemma lem1595154 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595155 (x : real) (y : real) (h1 : y = term25) : (term32 x y) = term25.
Proof. exact (TRANS (@lem1595152 x y h1) (@lem1595154)). Qed.
Lemma lem1595156 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595157 (x : real) (y : real) (h1 : y = term25) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1595156) (@lem1595155 x y h1)). Qed.
Lemma lem1595159 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1595160 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1595161 (y : real) (h1 : y = term25) : (real_inv y) = term33.
Proof. exact (MK_COMB (@lem1595160) (@lem1595159 y h1)). Qed.
Lemma lem1595163 : term33 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1595164 (y : real) (h1 : y = term25) : (real_inv y) = term25.
Proof. exact (TRANS (@lem1595161 y h1) (@lem1595163)). Qed.
Lemma lem1595165 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1595166 (x : real) (y : real) (h1 : y = term25) : (term37 x y) = (term41 x).
Proof. exact (MK_COMB (@lem1595165 x) (@lem1595164 y h1)). Qed.
Lemma lem1595168 (x : real) : (term40 x) = term25.
Proof. exact (EQ_MP (@lem1595124 x) (@lem1595123 x)). Qed.
Lemma lem1595169 (x : real) : (term41 x) = term25.
Proof. exact (@lem1595168 (real_inv x)). Qed.
Lemma lem1595170 (x : real) (y : real) (h1 : y = term25) : (term37 x y) = term25.
Proof. exact (TRANS (@lem1595166 x y h1) (@lem1595169 x)). Qed.
Lemma lem1595171 (x : real) (y : real) (h1 : y = term25) : ((term32 x y) = (term37 x y)) = (term25 = term25).
Proof. exact (MK_COMB (@lem1595157 x y h1) (@lem1595170 x y h1)). Qed.
Lemma lem1595173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595174 (x : real) : (x = x) = True.
Proof. exact (@lem1595173 real x). Qed.
Lemma lem1595175 : (term25 = term25) = True.
Proof. exact (@lem1595174 term25). Qed.
Lemma lem1595176 (x : real) (y : real) (h1 : y = term25) : ((term32 x y) = (term37 x y)) = True.
Proof. exact (TRANS (@lem1595171 x y h1) (@lem1595175)). Qed.
Lemma lem1595177 (x : real) (y : real) (h1 : y = term25) : True = ((term32 x y) = (term37 x y)).
Proof. exact (SYM (@lem1595176 x y h1)). Qed.
Lemma lem1595178 (x : real) (y : real) (h1 : y = term25) : (term32 x y) = (term37 x y).
Proof. exact (EQ_MP (@lem1595177 x y h1) (@lem0)). Qed.
Lemma lem1595216 (y : real) (x : real) : term16 y x.
Proof. exact (EQ_MP (@lem1594995 y x) (@lem1594994 y x)). Qed.
Lemma lem1595217 (x : real) (y : real) : term42 x y.
Proof. exact (@lem1595216 (real_mul x y) (term37 x y)). Qed.
Lemma lem1595221 (a : real) (c : real) (b : real) (d : real) : (term8 a b c d) = (term8 a c b d).
Proof. exact (EQ_MP (@lem1594972 a c b d) (@lem0)). Qed.
Lemma lem1595222 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1595221 (real_inv x) x (real_inv y) y). Qed.
Lemma lem1595223 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595224 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1595223) (@lem1595222 x y)). Qed.
Lemma lem1595225 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1595226 (x : real) (y : real) : ((term43 x y) = term17) = ((term44 x y) = term17).
Proof. exact (MK_COMB (@lem1595224 x y) (@lem1595225)). Qed.
Lemma lem1595227 (x : real) (y : real) : ((term44 x y) = term17) = ((term43 x y) = term17).
Proof. exact (SYM (@lem1595226 x y)). Qed.
Lemma lem1595229 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1594905 x) (@lem1594904 x)). Qed.
Lemma lem1595230 (y : real) : term3 y.
Proof. exact (@lem1595229 y). Qed.
Lemma lem1595231 (y : real) (h1 : term27 y) : (term47 y) = term17.
Proof. exact (@lem1595230 y (@lem1595006 y h1)). Qed.
Lemma lem1595233 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1594905 x) (@lem1594904 x)). Qed.
Lemma lem1595234 (x : real) (h1 : term27 x) : (term47 x) = term17.
Proof. exact (@lem1595233 x (@lem1595001 x h1)). Qed.
Lemma lem1595235 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1595236 (x : real) (y : real) (h1 : term27 y) : (term49 x y) = (term50 x).
Proof. exact (MK_COMB (@lem1595235 x) (@lem1595231 y h1)). Qed.
Lemma lem1595237 (x : real) : (term50 x) = ((term51 x) = term17).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1595238 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1595239 (y : real) (x : real) : ((term49 x y) = (term50 x)) = ((term49 x y) = ((term51 x) = term17)).
Proof. exact (MK_COMB (@lem1595238 x y) (@lem1595237 x)). Qed.
Lemma lem1595240 (x : real) (y : real) : (term49 x y) = ((term44 x y) = term17).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1595241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1595242 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1595241) (@lem1595240 x y)). Qed.
Lemma lem1595243 (x : real) : ((term51 x) = term17) = ((term51 x) = term17).
Proof. exact (eq_refl ((term51 x) = term17)). Qed.
Lemma lem1595244 (y : real) (x : real) : ((term49 x y) = ((term51 x) = term17)) = (((term44 x y) = term17) = ((term51 x) = term17)).
Proof. exact (MK_COMB (@lem1595242 x y) (@lem1595243 x)). Qed.
Lemma lem1595245 (y : real) (x : real) : ((term49 x y) = (term50 x)) = (((term44 x y) = term17) = ((term51 x) = term17)).
Proof. exact (TRANS (@lem1595239 y x) (@lem1595244 y x)). Qed.
Lemma lem1595246 (x : real) (y : real) (h1 : term27 y) : ((term44 x y) = term17) = ((term51 x) = term17).
Proof. exact (EQ_MP (@lem1595245 y x) (@lem1595236 x y h1)). Qed.
Lemma lem1595247 (x : real) (y : real) (h1 : term27 y) : ((term51 x) = term17) = ((term44 x y) = term17).
Proof. exact (SYM (@lem1595246 x y h1)). Qed.
Lemma lem1595248 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1595249 (x : real) (h1 : term27 x) : (term55 x) = term56.
Proof. exact (MK_COMB (@lem1595248) (@lem1595234 x h1)). Qed.
Lemma lem1595250 : term56 = (term57 = term17).
Proof. exact (eq_refl term56). Qed.
Lemma lem1595251 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1595252 (x : real) : ((term55 x) = term56) = ((term55 x) = (term57 = term17)).
Proof. exact (MK_COMB (@lem1595251 x) (@lem1595250)). Qed.
Lemma lem1595253 (x : real) : (term55 x) = ((term51 x) = term17).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1595254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1595255 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem1595254) (@lem1595253 x)). Qed.
Lemma lem1595256 : (term57 = term17) = (term57 = term17).
Proof. exact (eq_refl (term57 = term17)). Qed.
Lemma lem1595257 (x : real) : ((term55 x) = (term57 = term17)) = (((term51 x) = term17) = (term57 = term17)).
Proof. exact (MK_COMB (@lem1595255 x) (@lem1595256)). Qed.
Lemma lem1595258 (x : real) : ((term55 x) = term56) = (((term51 x) = term17) = (term57 = term17)).
Proof. exact (TRANS (@lem1595252 x) (@lem1595257 x)). Qed.
Lemma lem1595259 (x : real) (h1 : term27 x) : ((term51 x) = term17) = (term57 = term17).
Proof. exact (EQ_MP (@lem1595258 x) (@lem1595249 x h1)). Qed.
Lemma lem1595260 (x : real) (h1 : term27 x) : (term57 = term17) = ((term51 x) = term17).
Proof. exact (SYM (@lem1595259 x h1)). Qed.
Lemma lem1595264 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1594902 x) (@lem1594901 x)). Qed.
Lemma lem1595265 : term57 = term17.
Proof. exact (@lem1595264 term17). Qed.
Lemma lem1595266 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595267 : term60 = term61.
Proof. exact (MK_COMB (@lem1595266) (@lem1595265)). Qed.
Lemma lem1595268 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1595269 : (term57 = term17) = (term17 = term17).
Proof. exact (MK_COMB (@lem1595267) (@lem1595268)). Qed.
Lemma lem1595271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595272 (x : real) : (x = x) = True.
Proof. exact (@lem1595271 real x). Qed.
Lemma lem1595273 : (term17 = term17) = True.
Proof. exact (@lem1595272 term17). Qed.
Lemma lem1595274 : (term57 = term17) = True.
Proof. exact (TRANS (@lem1595269) (@lem1595273)). Qed.
Lemma lem1595275 : True = (term57 = term17).
Proof. exact (SYM (@lem1595274)). Qed.
Lemma lem1595276 : term57 = term17.
Proof. exact (EQ_MP (@lem1595275) (@lem0)). Qed.
Lemma lem1595277 (x : real) (h1 : term27 x) : (term51 x) = term17.
Proof. exact (EQ_MP (@lem1595260 x h1) (@lem1595276)). Qed.
Lemma lem1595278 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term44 x y) = term17.
Proof. exact (EQ_MP (@lem1595247 x y h2) (@lem1595277 x h1)). Qed.
Lemma lem1595279 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term43 x y) = term17.
Proof. exact (EQ_MP (@lem1595227 x y) (@lem1595278 x y h1 h2)). Qed.
Lemma lem1595281 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term32 x y) = (term37 x y).
Proof. exact (@lem1595217 x y (@lem1595279 x y h1 h2)). Qed.
Lemma lem1595282 (y : real) (x : real) (h1 : term27 x) : (term32 x y) = (term37 x y).
Proof. exact (or_elim (@lem1595004 y) (fun h0 : y = term25 => @lem1595178 x y h0) (fun h0 : term27 y => @lem1595281 x y h1 h0)). Qed.
Lemma lem1595283 (y : real) (x : real) (h1 : x = term25) : (term32 x y) = (term37 x y).
Proof. exact (or_elim (@lem1595004 y) (fun h0 : y = term25 => @lem1595061 x y h1 h0) (fun h0 : term27 y => @lem1595122 y x h1)). Qed.
Lemma lem1595284 (x : real) (y : real) : (term32 x y) = (term37 x y).
Proof. exact (or_elim (@lem1594999 x) (fun h0 : x = term25 => @lem1595283 y x h0) (fun h0 : term27 x => @lem1595282 y x h0)). Qed.
Lemma lem1595289 (x : real) : term62 x.
Proof. exact (fun y : real => @lem1595284 x y). Qed.
Lemma lem1595294 : term63.
Proof. exact (fun x : real => @lem1595289 x). Qed.
