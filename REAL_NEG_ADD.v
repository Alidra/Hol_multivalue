Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_ADD_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Require Import REAL_EQ_ADD_RCANCEL_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm37_spec.
Lemma lem1360914 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1360915 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1360917 (x : real) : term2 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1360918 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1360920 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1360921 {A : Type'} (x : A) : (term5 A x) = ((x = x) = True).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem1360923 (n : real) (m : real) (p : real) : term6 n m p.
Proof. exact (proj2 (@lem1352530 n m p)). Qed.
Lemma lem1360930 (m : real) (n : real) (p : real) : (term7 m n p) = (term8 m n p).
Proof. exact (proj1 (@lem1360923 n m p)). Qed.
Lemma lem1360931 (a : real) (b : real) (c : real) (d : real) : (term9 a b c d) = (term10 a b c d).
Proof. exact (@lem1360930 a b (real_add c d)). Qed.
Lemma lem1360947 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1360948 (a : real) (b : real) (c : real) (d : real) : (term11 a b c d) = (term12 a b c d).
Proof. exact (MK_COMB (@lem1360947) (@lem1360931 a b c d)). Qed.
Lemma lem1360950 (m : real) (n : real) (p : real) : (term7 m n p) = (term8 m n p).
Proof. exact (proj1 (@lem1360923 n m p)). Qed.
Lemma lem1360951 (a : real) (c : real) (b : real) (d : real) : (term9 a c b d) = (term10 a c b d).
Proof. exact (@lem1360950 a c (real_add b d)). Qed.
Lemma lem1360959 (n : real) (m : real) (p : real) : (term8 m n p) = (term8 n m p).
Proof. exact (proj2 (@lem1360923 n m p)). Qed.
Lemma lem1360960 (b : real) (c : real) (d : real) : (term8 c b d) = (term8 b c d).
Proof. exact (@lem1360959 b c d). Qed.
Lemma lem1360970 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem1360971 (a : real) (b : real) (c : real) (d : real) : (term10 a c b d) = (term10 a b c d).
Proof. exact (MK_COMB (@lem1360970 a) (@lem1360960 b c d)). Qed.
Lemma lem1360978 (a : real) (b : real) (c : real) (d : real) : (term9 a c b d) = (term10 a b c d).
Proof. exact (TRANS (@lem1360951 a c b d) (@lem1360971 a b c d)). Qed.
Lemma lem1360979 (a : real) (b : real) (c : real) (d : real) : ((term9 a b c d) = (term9 a c b d)) = ((term10 a b c d) = (term10 a b c d)).
Proof. exact (MK_COMB (@lem1360948 a b c d) (@lem1360978 a b c d)). Qed.
Lemma lem1360981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1360921 A x) (@lem1360920 A x)). Qed.
Lemma lem1360982 (x : real) : (x = x) = True.
Proof. exact (@lem1360981 real x). Qed.
Lemma lem1360983 (a : real) (b : real) (c : real) (d : real) : ((term10 a b c d) = (term10 a b c d)) = True.
Proof. exact (@lem1360982 (term10 a b c d)). Qed.
Lemma lem1360984 (a : real) (c : real) (b : real) (d : real) : ((term9 a b c d) = (term9 a c b d)) = True.
Proof. exact (TRANS (@lem1360979 a b c d) (@lem1360983 a b c d)). Qed.
Lemma lem1360985 (a : real) (c : real) (b : real) (d : real) : True = ((term9 a b c d) = (term9 a c b d)).
Proof. exact (SYM (@lem1360984 a c b d)). Qed.
Lemma lem1360987 (x : real) : term2 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1360988 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1360990 (x : real) : term13 x.
Proof. exact (@lem1355147 x). Qed.
Lemma lem1360991 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1360992 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1360991 x) (@lem1360990 x)). Qed.
Lemma lem1360993 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1360992 x y). Qed.
Lemma lem1360994 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1360995 (x : real) (y : real) : term16 x y.
Proof. exact (EQ_MP (@lem1360994 x y) (@lem1360993 x y)). Qed.
Lemma lem1360996 (x : real) (y : real) (z : real) : term17 x y z.
Proof. exact (@lem1360995 x y z). Qed.
Lemma lem1360997 (z : real) (x : real) (y : real) : (term17 x y z) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (term17 x y z)). Qed.
Lemma lem1360998 (z : real) (x : real) (y : real) : ((real_add x z) = (real_add y z)) = (x = y).
Proof. exact (EQ_MP (@lem1360997 z x y) (@lem1360996 x y z)). Qed.
Lemma lem1361001 (z : real) (x : real) (y : real) : term18 z x y.
Proof. exact (@lem37 ((real_add x z) = (real_add y z)) (x = y)). Qed.
Lemma lem1361002 (z : real) (x : real) (y : real) : term19 z x y.
Proof. exact (@lem1361001 z x y (@lem1360998 z x y)). Qed.
Lemma lem1361003 (z : real) (x : real) : term20 z x.
Proof. exact (fun y : real => @lem1361002 z x y). Qed.
Lemma lem1361004 (z : real) : term21 z.
Proof. exact (fun x : real => @lem1361003 z x). Qed.
Lemma lem1361005 : term22.
Proof. exact (fun z : real => @lem1361004 z). Qed.
Lemma lem1361006 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1361007 (z : real) (h1 : term22) : term23 z.
Proof. exact (@lem1361006 h1 z). Qed.
Lemma lem1361008 (z : real) : (term23 z) = (term21 z).
Proof. exact (eq_refl (term23 z)). Qed.
Lemma lem1361009 (z : real) (h1 : term22) : term21 z.
Proof. exact (EQ_MP (@lem1361008 z) (@lem1361007 z h1)). Qed.
Lemma lem1361010 (z : real) (x : real) (h1 : term22) : term24 z x.
Proof. exact (@lem1361009 z h1 x). Qed.
Lemma lem1361011 (z : real) (x : real) : (term24 z x) = (term20 z x).
Proof. exact (eq_refl (term24 z x)). Qed.
Lemma lem1361012 (z : real) (x : real) (h1 : term22) : term20 z x.
Proof. exact (EQ_MP (@lem1361011 z x) (@lem1361010 z x h1)). Qed.
Lemma lem1361013 (z : real) (x : real) (y : real) (h1 : term22) : term25 z x y.
Proof. exact (@lem1361012 z x h1 y). Qed.
Lemma lem1361014 (z : real) (x : real) (y : real) : (term25 z x y) = (term19 z x y).
Proof. exact (eq_refl (term25 z x y)). Qed.
Lemma lem1361015 (z : real) (x : real) (y : real) (h1 : term22) : term19 z x y.
Proof. exact (EQ_MP (@lem1361014 z x y) (@lem1361013 z x y h1)). Qed.
Lemma lem1361016 (x : real) (y : real) (z : real) (h1 : (real_add x z) = (real_add y z)) : (real_add x z) = (real_add y z).
Proof. exact (h1). Qed.
Lemma lem1361017 (x : real) (y : real) (z : real) (h1 : term22) (h2 : (real_add x z) = (real_add y z)) : x = y.
Proof. exact (@lem1361015 z x y h1 (@lem1361016 x y z h2)). Qed.
Lemma lem1361018 (x : real) (y : real) (z : real) (h1 : (real_add x z) = (real_add y z)) : term26 x y.
Proof. exact (fun h0 : term22 => @lem1361017 x y z h0 h1). Qed.
Lemma lem1361019 (x : real) (y : real) (h1 : term27 x y) : term27 x y.
Proof. exact (h1). Qed.
Lemma lem1361020 (x : real) (y : real) (h1 : term27 x y) : term26 x y.
Proof. exact (ex_elim (@lem1361019 x y h1) (fun z : real => fun h0 : term28 x y z => @lem1361018 x y z h0)). Qed.
Lemma lem1361021 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1361022 (x : real) (y : real) (h1 : term22) (h2 : term27 x y) : x = y.
Proof. exact (@lem1361020 x y h2 (@lem1361021 h1)). Qed.
Lemma lem1361023 (x : real) (y : real) (h1 : term22) : term29 x y.
Proof. exact (fun h0 : term27 x y => @lem1361022 x y h1 h0). Qed.
Lemma lem1361024 (x : real) (h1 : term22) : term30 x.
Proof. exact (fun y : real => @lem1361023 x y h1). Qed.
Lemma lem1361025 (h1 : term22) : term31.
Proof. exact (fun x : real => @lem1361024 x h1). Qed.
Lemma lem1361026 : term32.
Proof. exact (fun h0 : term22 => @lem1361025 h0). Qed.
Lemma lem1361027 : term31.
Proof. exact (@lem1361026 (@lem1361005)). Qed.
Lemma lem1361028 (x : real) : term33 x.
Proof. exact (@lem1361027 x). Qed.
Lemma lem1361029 (x : real) : (term33 x) = (term30 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1361030 (x : real) : term30 x.
Proof. exact (EQ_MP (@lem1361029 x) (@lem1361028 x)). Qed.
Lemma lem1361031 (x : real) (y : real) : term34 x y.
Proof. exact (@lem1361030 x y). Qed.
Lemma lem1361032 (x : real) (y : real) : (term34 x y) = (term29 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1361035 (x : real) (y : real) : term29 x y.
Proof. exact (EQ_MP (@lem1361032 x y) (@lem1361031 x y)). Qed.
Lemma lem1361036 (x : real) (y : real) : term35 x y.
Proof. exact (@lem1361035 (term36 x y) (term37 x y)). Qed.
Lemma lem1361040 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1360988 x) (@lem1360987 x)). Qed.
Lemma lem1361041 (x : real) (y : real) : (term38 x y) = term4.
Proof. exact (@lem1361040 (real_add x y)). Qed.
Lemma lem1361042 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1361043 (x : real) (y : real) : (term39 x y) = term40.
Proof. exact (MK_COMB (@lem1361042) (@lem1361041 x y)). Qed.
Lemma lem1361046 (x : real) (y : real) : (term41 x y) = (term41 x y).
Proof. exact (eq_refl (term41 x y)). Qed.
Lemma lem1361047 (x : real) (y : real) : ((term38 x y) = (term41 x y)) = (term4 = (term41 x y)).
Proof. exact (MK_COMB (@lem1361043 x y) (@lem1361046 x y)). Qed.
Lemma lem1361050 (x : real) (y : real) : (term4 = (term41 x y)) = ((term38 x y) = (term41 x y)).
Proof. exact (SYM (@lem1361047 x y)). Qed.
Lemma lem1361054 (a : real) (c : real) (b : real) (d : real) : (term9 a b c d) = (term9 a c b d).
Proof. exact (EQ_MP (@lem1360985 a c b d) (@lem0)). Qed.
Lemma lem1361055 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (@lem1361054 (real_neg x) x (real_neg y) y). Qed.
Lemma lem1361056 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem1361057 (x : real) (y : real) : (term4 = (term41 x y)) = (term4 = (term42 x y)).
Proof. exact (MK_COMB (@lem1361056) (@lem1361055 x y)). Qed.
Lemma lem1361058 (x : real) (y : real) : (term4 = (term42 x y)) = (term4 = (term41 x y)).
Proof. exact (SYM (@lem1361057 x y)). Qed.
Lemma lem1361062 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1360918 x) (@lem1360917 x)). Qed.
Lemma lem1361063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1361064 (x : real) : (term43 x) = term44.
Proof. exact (MK_COMB (@lem1361063) (@lem1361062 x)). Qed.
Lemma lem1361066 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1360918 x) (@lem1360917 x)). Qed.
Lemma lem1361067 (y : real) : (term3 y) = term4.
Proof. exact (@lem1361066 y). Qed.
Lemma lem1361068 (x : real) (y : real) : (term42 x y) = term45.
Proof. exact (MK_COMB (@lem1361064 x) (@lem1361067 y)). Qed.
Lemma lem1361070 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1360915 x) (@lem1360914 x)). Qed.
Lemma lem1361071 : term45 = term4.
Proof. exact (@lem1361070 term4). Qed.
Lemma lem1361072 (x : real) (y : real) : (term42 x y) = term4.
Proof. exact (TRANS (@lem1361068 x y) (@lem1361071)). Qed.
Lemma lem1361073 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem1361074 (x : real) (y : real) : (term4 = (term42 x y)) = (term4 = term4).
Proof. exact (MK_COMB (@lem1361073) (@lem1361072 x y)). Qed.
Lemma lem1361076 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1361077 (x : real) : (x = x) = True.
Proof. exact (@lem1361076 real x). Qed.
Lemma lem1361078 : (term4 = term4) = True.
Proof. exact (@lem1361077 term4). Qed.
Lemma lem1361079 (x : real) (y : real) : (term4 = (term42 x y)) = True.
Proof. exact (TRANS (@lem1361074 x y) (@lem1361078)). Qed.
Lemma lem1361080 (x : real) (y : real) : True = (term4 = (term42 x y)).
Proof. exact (SYM (@lem1361079 x y)). Qed.
Lemma lem1361081 (x : real) (y : real) : term4 = (term42 x y).
Proof. exact (EQ_MP (@lem1361080 x y) (@lem0)). Qed.
Lemma lem1361082 (x : real) (y : real) : term4 = (term41 x y).
Proof. exact (EQ_MP (@lem1361058 x y) (@lem1361081 x y)). Qed.
Lemma lem1361083 (x : real) (y : real) : (term38 x y) = (term41 x y).
Proof. exact (EQ_MP (@lem1361050 x y) (@lem1361082 x y)). Qed.
Lemma lem1361084 (x : real) (y : real) : term46 x y.
Proof. exact (ex_intro (term47 x y) (real_add x y) (@lem1361083 x y)). Qed.
Lemma lem1361085 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem1361036 x y (@lem1361084 x y)). Qed.
Lemma lem1361090 (x : real) : term48 x.
Proof. exact (fun y : real => @lem1361085 x y). Qed.
Lemma lem1361095 : term49.
Proof. exact (fun x : real => @lem1361090 x). Qed.
