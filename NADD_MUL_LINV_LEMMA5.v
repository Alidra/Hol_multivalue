Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA5_term_abbrevs.
Require Import LE_ADD_spec.
Require Import LE_ADD2_spec.
Require Import LE_ADDR_spec.
Require Import LE_MULT2_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_AC_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_SYM_spec.
Require Import NADD_CAUCHY_spec.
Require Import NADD_MUL_LINV_LEMMA4_spec.
Require Import NADD_UBOUND_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1302949 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1302950 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1302949 h1 m). Qed.
Lemma lem1302951 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1302952 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1302951 m) (@lem1302950 m h1)). Qed.
Lemma lem1302953 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1302952 m h1 n). Qed.
Lemma lem1302954 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1302955 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1302954 n m) (@lem1302953 m n h1)). Qed.
Lemma lem1302956 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1302955 n m h1 p). Qed.
Lemma lem1302957 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1302958 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1302957 n m p) (@lem1302956 n m p h1)). Qed.
Lemma lem1302959 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1302960 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1302958 n m p h1 (@lem1302959 m n p h2)). Qed.
Lemma lem1302961 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1302960 m n p h0 h1). Qed.
Lemma lem1302962 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1302963 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1302962 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1302961 m n p h0)). Qed.
Lemma lem1302964 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1302965 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1302963 m p h2 (@lem1302964 h1)). Qed.
Lemma lem1302966 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1302965 m p h1 h0). Qed.
Lemma lem1302967 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1302966 m p h1). Qed.
Lemma lem1302968 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1302967 m h1). Qed.
Lemma lem1302969 : term14.
Proof. exact (fun h0 : term0 => @lem1302968 h0). Qed.
Lemma lem1302970 : term13.
Proof. exact (@lem1302969 (@lem93743)). Qed.
Lemma lem1302971 (m : nat) : term15 m.
Proof. exact (@lem1302970 m). Qed.
Lemma lem1302972 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1302973 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1302972 m) (@lem1302971 m)). Qed.
Lemma lem1302974 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1302973 m p). Qed.
Lemma lem1302975 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1302977 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1302978 (m : nat) (h1 : term17) : term18 m.
Proof. exact (@lem1302977 h1 m). Qed.
Lemma lem1302979 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1302980 (m : nat) (h1 : term17) : term19 m.
Proof. exact (EQ_MP (@lem1302979 m) (@lem1302978 m h1)). Qed.
Lemma lem1302981 (m : nat) (n : nat) (h1 : term17) : term20 m n.
Proof. exact (@lem1302980 m h1 n). Qed.
Lemma lem1302982 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1302983 (m : nat) (n : nat) (h1 : term17) : term21 m n.
Proof. exact (EQ_MP (@lem1302982 m n) (@lem1302981 m n h1)). Qed.
Lemma lem1302984 (m : nat) (n : nat) (p : nat) (h1 : term17) : term22 m n p.
Proof. exact (@lem1302983 m n h1 p). Qed.
Lemma lem1302985 (m : nat) (p : nat) (n : nat) : (term22 m n p) = (term23 m p n).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem1302986 (m : nat) (p : nat) (n : nat) (h1 : term17) : term23 m p n.
Proof. exact (EQ_MP (@lem1302985 m p n) (@lem1302984 m n p h1)). Qed.
Lemma lem1302987 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term24 m p n q.
Proof. exact (@lem1302986 m p n h1 q). Qed.
Lemma lem1302988 (m : nat) (p : nat) (n : nat) (q : nat) : (term24 m p n q) = (term25 m p n q).
Proof. exact (eq_refl (term24 m p n q)). Qed.
Lemma lem1302989 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term25 m p n q.
Proof. exact (EQ_MP (@lem1302988 m p n q) (@lem1302987 m p n q h1)). Qed.
Lemma lem1302990 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term26 m n p q) : term26 m n p q.
Proof. exact (h1). Qed.
Lemma lem1302991 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17) (h2 : term26 m n p q) : term27 m p n q.
Proof. exact (@lem1302989 m p n q h1 (@lem1302990 m n p q h2)). Qed.
Lemma lem1302992 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term26 m n p q) : term28 m p n q.
Proof. exact (fun h0 : term17 => @lem1302991 m n p q h0 h1). Qed.
Lemma lem1302993 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1302994 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term17) (h2 : term26 m n p q) : term27 m p n q.
Proof. exact (@lem1302992 m n p q h2 (@lem1302993 h1)). Qed.
Lemma lem1302995 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term17) : term25 m p n q.
Proof. exact (fun h0 : term26 m n p q => @lem1302994 m n p q h1 h0). Qed.
Lemma lem1302996 (m : nat) (p : nat) (n : nat) (h1 : term17) : term23 m p n.
Proof. exact (fun q : nat => @lem1302995 m p n q h1). Qed.
Lemma lem1302997 (m : nat) (p : nat) (h1 : term17) : term29 m p.
Proof. exact (fun n : nat => @lem1302996 m p n h1). Qed.
Lemma lem1302998 (m : nat) (h1 : term17) : term30 m.
Proof. exact (fun p : nat => @lem1302997 m p h1). Qed.
Lemma lem1302999 (h1 : term17) : term31.
Proof. exact (fun m : nat => @lem1302998 m h1). Qed.
Lemma lem1303000 : term32.
Proof. exact (fun h0 : term17 => @lem1302999 h0). Qed.
Lemma lem1303001 : term31.
Proof. exact (@lem1303000 (@lem102387)). Qed.
Lemma lem1303002 (m : nat) : term33 m.
Proof. exact (@lem1303001 m). Qed.
Lemma lem1303003 (m : nat) : (term33 m) = (term30 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1303004 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1303003 m) (@lem1303002 m)). Qed.
Lemma lem1303005 (m : nat) (p : nat) : term34 m p.
Proof. exact (@lem1303004 m p). Qed.
Lemma lem1303006 (m : nat) (p : nat) : (term34 m p) = (term29 m p).
Proof. exact (eq_refl (term34 m p)). Qed.
Lemma lem1303007 (m : nat) (p : nat) : term29 m p.
Proof. exact (EQ_MP (@lem1303006 m p) (@lem1303005 m p)). Qed.
Lemma lem1303008 (m : nat) (p : nat) (n : nat) : term35 m p n.
Proof. exact (@lem1303007 m p n). Qed.
Lemma lem1303009 (m : nat) (p : nat) (n : nat) : (term35 m p n) = (term23 m p n).
Proof. exact (eq_refl (term35 m p n)). Qed.
Lemma lem1303010 (m : nat) (p : nat) (n : nat) : term23 m p n.
Proof. exact (EQ_MP (@lem1303009 m p n) (@lem1303008 m p n)). Qed.
Lemma lem1303011 (m : nat) (p : nat) (n : nat) (q : nat) : term24 m p n q.
Proof. exact (@lem1303010 m p n q). Qed.
Lemma lem1303012 (m : nat) (p : nat) (n : nat) (q : nat) : (term24 m p n q) = (term25 m p n q).
Proof. exact (eq_refl (term24 m p n q)). Qed.
Lemma lem1303014 (m : nat) : term36 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem1303015 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1303016 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1303015 m) (@lem1303014 m)). Qed.
Lemma lem1303017 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1303016 m n). Qed.
Lemma lem1303018 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1303019 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1303018 m n) (@lem1303017 m n)). Qed.
Lemma lem1303020 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1303019 m n p). Qed.
Lemma lem1303021 (m : nat) (n : nat) (p : nat) : (term40 m n p) = ((term41 m n p) = (term42 m n p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1303023 {A : Type'} (x : A) : term43 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1303024 {A : Type'} (x : A) : (term43 A x) = ((x = x) = True).
Proof. exact (eq_refl (term43 A x)). Qed.
Lemma lem1303026 (n : nat) (m : nat) (p : nat) : term44 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1303033 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1303026 n m p)). Qed.
Lemma lem1303034 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term47 a b c d e) = (term48 a b c d e).
Proof. exact (@lem1303033 a b (term45 c d e)). Qed.
Lemma lem1303048 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1303026 n m p)). Qed.
Lemma lem1303049 (c : nat) (d : nat) (e : nat) : (term45 c d e) = (term46 c d e).
Proof. exact (@lem1303048 c d e). Qed.
Lemma lem1303059 (b : nat) : (Nat.mul b) = (Nat.mul b).
Proof. exact (eq_refl (Nat.mul b)). Qed.
Lemma lem1303060 (b : nat) (c : nat) (d : nat) (e : nat) : (term49 b c d e) = (term50 b c d e).
Proof. exact (MK_COMB (@lem1303059 b) (@lem1303049 c d e)). Qed.
Lemma lem1303067 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem1303068 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term48 a b c d e) = (term51 a b c d e).
Proof. exact (MK_COMB (@lem1303067 a) (@lem1303060 b c d e)). Qed.
Lemma lem1303075 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term47 a b c d e) = (term51 a b c d e).
Proof. exact (TRANS (@lem1303034 a b c d e) (@lem1303068 a b c d e)). Qed.
Lemma lem1303076 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1303077 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term52 a b c d e) = (term53 a b c d e).
Proof. exact (MK_COMB (@lem1303076) (@lem1303075 a b c d e)). Qed.
Lemma lem1303079 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1303026 n m p)). Qed.
Lemma lem1303080 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : (term54 a c b d e) = (term47 a c b d e).
Proof. exact (@lem1303079 (Nat.mul a c) (Nat.mul b d) e). Qed.
Lemma lem1303082 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1303026 n m p)). Qed.
Lemma lem1303083 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : (term47 a c b d e) = (term48 a c b d e).
Proof. exact (@lem1303082 a c (term45 b d e)). Qed.
Lemma lem1303090 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : (term54 a c b d e) = (term48 a c b d e).
Proof. exact (TRANS (@lem1303080 a c b d e) (@lem1303083 a c b d e)). Qed.
Lemma lem1303098 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (proj1 (@lem1303026 n m p)). Qed.
Lemma lem1303099 (b : nat) (d : nat) (e : nat) : (term45 b d e) = (term46 b d e).
Proof. exact (@lem1303098 b d e). Qed.
Lemma lem1303109 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem1303110 (c : nat) (b : nat) (d : nat) (e : nat) : (term49 c b d e) = (term50 c b d e).
Proof. exact (MK_COMB (@lem1303109 c) (@lem1303099 b d e)). Qed.
Lemma lem1303112 (n : nat) (m : nat) (p : nat) : (term46 m n p) = (term46 n m p).
Proof. exact (proj2 (@lem1303026 n m p)). Qed.
Lemma lem1303113 (b : nat) (c : nat) (d : nat) (e : nat) : (term50 c b d e) = (term50 b c d e).
Proof. exact (@lem1303112 b c (Nat.mul d e)). Qed.
Lemma lem1303129 (b : nat) (c : nat) (d : nat) (e : nat) : (term49 c b d e) = (term50 b c d e).
Proof. exact (TRANS (@lem1303110 c b d e) (@lem1303113 b c d e)). Qed.
Lemma lem1303130 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem1303131 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term48 a c b d e) = (term51 a b c d e).
Proof. exact (MK_COMB (@lem1303130 a) (@lem1303129 b c d e)). Qed.
Lemma lem1303138 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term54 a c b d e) = (term51 a b c d e).
Proof. exact (TRANS (@lem1303090 a c b d e) (@lem1303131 a b c d e)). Qed.
Lemma lem1303139 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term47 a b c d e) = (term54 a c b d e)) = ((term51 a b c d e) = (term51 a b c d e)).
Proof. exact (MK_COMB (@lem1303077 a b c d e) (@lem1303138 a b c d e)). Qed.
Lemma lem1303141 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1303024 A x) (@lem1303023 A x)). Qed.
Lemma lem1303142 (x : nat) : (x = x) = True.
Proof. exact (@lem1303141 nat x). Qed.
Lemma lem1303143 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term51 a b c d e) = (term51 a b c d e)) = True.
Proof. exact (@lem1303142 (term51 a b c d e)). Qed.
Lemma lem1303144 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : ((term47 a b c d e) = (term54 a c b d e)) = True.
Proof. exact (TRANS (@lem1303139 a b c d e) (@lem1303143 a b c d e)). Qed.
Lemma lem1303145 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : True = ((term47 a b c d e) = (term54 a c b d e)).
Proof. exact (SYM (@lem1303144 a c b d e)). Qed.
Lemma lem1303147 (m : nat) : term55 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1303148 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem1303149 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem1303148 m) (@lem1303147 m)). Qed.
Lemma lem1303150 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem1303149 m n). Qed.
Lemma lem1303151 (n : nat) (m : nat) : (term57 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem1303156 (m : nat) (n : nat) (p : nat) (h1 : (term46 m n p) = (term45 m n p)) : (term46 m n p) = (term45 m n p).
Proof. exact (h1). Qed.
Lemma lem1303157 (m : nat) (n : nat) (p : nat) (h1 : (term46 m n p) = (term45 m n p)) : (term45 m n p) = (term46 m n p).
Proof. exact (SYM (@lem1303156 m n p h1)). Qed.
Lemma lem1303158 (m : nat) (n : nat) (p : nat) (h1 : (term45 m n p) = (term46 m n p)) : (term45 m n p) = (term46 m n p).
Proof. exact (h1). Qed.
Lemma lem1303159 (m : nat) (n : nat) (p : nat) (h1 : (term45 m n p) = (term46 m n p)) : (term46 m n p) = (term45 m n p).
Proof. exact (SYM (@lem1303158 m n p h1)). Qed.
Lemma lem1303160 (m : nat) (n : nat) (p : nat) : ((term46 m n p) = (term45 m n p)) = ((term45 m n p) = (term46 m n p)).
Proof. exact (prop_ext (fun h1 : (term46 m n p) = (term45 m n p) => @lem1303157 m n p h1) (fun h1 : (term45 m n p) = (term46 m n p) => @lem1303159 m n p h1)). Qed.
Lemma lem1303161 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (fun_ext (fun p : nat => @lem1303160 m n p)). Qed.
Lemma lem1303162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1303163 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem1303162) (@lem1303161 m n)). Qed.
Lemma lem1303164 (m : nat) : (term62 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem1303163 m n)). Qed.
Lemma lem1303165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1303166 (m : nat) : (term64 m) = (term65 m).
Proof. exact (MK_COMB (@lem1303165) (@lem1303164 m)). Qed.
Lemma lem1303167 : term66 = term67.
Proof. exact (fun_ext (fun m : nat => @lem1303166 m)). Qed.
Lemma lem1303168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1303169 : term68 = term69.
Proof. exact (MK_COMB (@lem1303168) (@lem1303167)). Qed.
Lemma lem1303170 : term69.
Proof. exact (EQ_MP (@lem1303169) (@lem82357)). Qed.
Lemma lem1303171 (m : nat) : term70 m.
Proof. exact (@lem1303170 m). Qed.
Lemma lem1303172 (m : nat) : (term70 m) = (term65 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem1303173 (m : nat) : term65 m.
Proof. exact (EQ_MP (@lem1303172 m) (@lem1303171 m)). Qed.
Lemma lem1303174 (m : nat) (n : nat) : term71 m n.
Proof. exact (@lem1303173 m n). Qed.
Lemma lem1303175 (m : nat) (n : nat) : (term71 m n) = (term61 m n).
Proof. exact (eq_refl (term71 m n)). Qed.
Lemma lem1303176 (m : nat) (n : nat) : term61 m n.
Proof. exact (EQ_MP (@lem1303175 m n) (@lem1303174 m n)). Qed.
Lemma lem1303177 (m : nat) (n : nat) (p : nat) : term72 m n p.
Proof. exact (@lem1303176 m n p). Qed.
Lemma lem1303178 (m : nat) (n : nat) (p : nat) : (term72 m n p) = ((term45 m n p) = (term46 m n p)).
Proof. exact (eq_refl (term72 m n p)). Qed.
Lemma lem1303180 (m : nat) : term55 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1303181 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem1303182 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem1303181 m) (@lem1303180 m)). Qed.
Lemma lem1303183 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem1303182 m n). Qed.
Lemma lem1303184 (n : nat) (m : nat) : (term57 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem1303186 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1303187 (m : nat) (h1 : term73) : term74 m.
Proof. exact (@lem1303186 h1 m). Qed.
Lemma lem1303188 (m : nat) : (term74 m) = (term75 m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem1303189 (m : nat) (h1 : term73) : term75 m.
Proof. exact (EQ_MP (@lem1303188 m) (@lem1303187 m h1)). Qed.
Lemma lem1303190 (m : nat) (n : nat) (h1 : term73) : term76 m n.
Proof. exact (@lem1303189 m h1 n). Qed.
Lemma lem1303191 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem1303192 (m : nat) (n : nat) (h1 : term73) : term77 m n.
Proof. exact (EQ_MP (@lem1303191 m n) (@lem1303190 m n h1)). Qed.
Lemma lem1303193 (m : nat) (n : nat) (p : nat) (h1 : term73) : term78 m n p.
Proof. exact (@lem1303192 m n h1 p). Qed.
Lemma lem1303194 (m : nat) (n : nat) (p : nat) : (term78 m n p) = (term79 m n p).
Proof. exact (eq_refl (term78 m n p)). Qed.
Lemma lem1303195 (m : nat) (n : nat) (p : nat) (h1 : term73) : term79 m n p.
Proof. exact (EQ_MP (@lem1303194 m n p) (@lem1303193 m n p h1)). Qed.
Lemma lem1303196 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term73) : term80 m n p q.
Proof. exact (@lem1303195 m n p h1 q). Qed.
Lemma lem1303197 (m : nat) (n : nat) (p : nat) (q : nat) : (term80 m n p q) = (term81 m n p q).
Proof. exact (eq_refl (term80 m n p q)). Qed.
Lemma lem1303198 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term73) : term81 m n p q.
Proof. exact (EQ_MP (@lem1303197 m n p q) (@lem1303196 m n p q h1)). Qed.
Lemma lem1303199 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term26 m p n q) : term26 m p n q.
Proof. exact (h1). Qed.
Lemma lem1303200 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term73) (h2 : term26 m p n q) : term82 m n p q.
Proof. exact (@lem1303198 m n p q h1 (@lem1303199 m p n q h2)). Qed.
Lemma lem1303201 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term26 m p n q) : term83 m n p q.
Proof. exact (fun h0 : term73 => @lem1303200 m p n q h0 h1). Qed.
Lemma lem1303202 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1303203 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term73) (h2 : term26 m p n q) : term82 m n p q.
Proof. exact (@lem1303201 m p n q h2 (@lem1303202 h1)). Qed.
Lemma lem1303204 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term73) : term81 m n p q.
Proof. exact (fun h0 : term26 m p n q => @lem1303203 m p n q h1 h0). Qed.
Lemma lem1303205 (m : nat) (n : nat) (p : nat) (h1 : term73) : term79 m n p.
Proof. exact (fun q : nat => @lem1303204 m n p q h1). Qed.
Lemma lem1303206 (m : nat) (n : nat) (h1 : term73) : term77 m n.
Proof. exact (fun p : nat => @lem1303205 m n p h1). Qed.
Lemma lem1303207 (m : nat) (h1 : term73) : term75 m.
Proof. exact (fun n : nat => @lem1303206 m n h1). Qed.
Lemma lem1303208 (h1 : term73) : term73.
Proof. exact (fun m : nat => @lem1303207 m h1). Qed.
Lemma lem1303209 : term84.
Proof. exact (fun h0 : term73 => @lem1303208 h0). Qed.
Lemma lem1303210 : term73.
Proof. exact (@lem1303209 (@lem101399)). Qed.
Lemma lem1303211 (m : nat) : term74 m.
Proof. exact (@lem1303210 m). Qed.
Lemma lem1303212 (m : nat) : (term74 m) = (term75 m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem1303213 (m : nat) : term75 m.
Proof. exact (EQ_MP (@lem1303212 m) (@lem1303211 m)). Qed.
Lemma lem1303214 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1303213 m n). Qed.
Lemma lem1303215 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem1303216 (m : nat) (n : nat) : term77 m n.
Proof. exact (EQ_MP (@lem1303215 m n) (@lem1303214 m n)). Qed.
Lemma lem1303217 (m : nat) (n : nat) (p : nat) : term78 m n p.
Proof. exact (@lem1303216 m n p). Qed.
Lemma lem1303218 (m : nat) (n : nat) (p : nat) : (term78 m n p) = (term79 m n p).
Proof. exact (eq_refl (term78 m n p)). Qed.
Lemma lem1303219 (m : nat) (n : nat) (p : nat) : term79 m n p.
Proof. exact (EQ_MP (@lem1303218 m n p) (@lem1303217 m n p)). Qed.
Lemma lem1303220 (m : nat) (n : nat) (p : nat) (q : nat) : term80 m n p q.
Proof. exact (@lem1303219 m n p q). Qed.
Lemma lem1303221 (m : nat) (n : nat) (p : nat) (q : nat) : (term80 m n p q) = (term81 m n p q).
Proof. exact (eq_refl (term80 m n p q)). Qed.
Lemma lem1303223 (m : nat) : term85 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1303224 (m : nat) : (term85 m) = (term86 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem1303225 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem1303224 m) (@lem1303223 m)). Qed.
Lemma lem1303226 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem1303225 m n). Qed.
Lemma lem1303227 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem1303228 (m : nat) (n : nat) : term88 m n.
Proof. exact (EQ_MP (@lem1303227 m n) (@lem1303226 m n)). Qed.
Lemma lem1303229 (m : nat) (n : nat) (p : nat) : term89 m n p.
Proof. exact (@lem1303228 m n p). Qed.
Lemma lem1303230 (m : nat) (n : nat) (p : nat) : (term89 m n p) = ((term90 m n p) = (term91 m n p)).
Proof. exact (eq_refl (term89 m n p)). Qed.
Lemma lem1303232 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303233 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1303232 h1 m). Qed.
Lemma lem1303234 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1303235 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1303234 m) (@lem1303233 m h1)). Qed.
Lemma lem1303236 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1303235 m h1 n). Qed.
Lemma lem1303237 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1303238 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1303237 n m) (@lem1303236 m n h1)). Qed.
Lemma lem1303239 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1303238 n m h1 p). Qed.
Lemma lem1303240 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1303241 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1303240 n m p) (@lem1303239 n m p h1)). Qed.
Lemma lem1303242 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1303243 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1303241 n m p h1 (@lem1303242 m n p h2)). Qed.
Lemma lem1303244 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1303243 m n p h0 h1). Qed.
Lemma lem1303245 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1303246 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1303245 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1303244 m n p h0)). Qed.
Lemma lem1303247 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303248 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1303246 m p h2 (@lem1303247 h1)). Qed.
Lemma lem1303249 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1303248 m p h1 h0). Qed.
Lemma lem1303250 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1303249 m p h1). Qed.
Lemma lem1303251 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1303250 m h1). Qed.
Lemma lem1303252 : term14.
Proof. exact (fun h0 : term0 => @lem1303251 h0). Qed.
Lemma lem1303253 : term13.
Proof. exact (@lem1303252 (@lem93743)). Qed.
Lemma lem1303254 (m : nat) : term15 m.
Proof. exact (@lem1303253 m). Qed.
Lemma lem1303255 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1303256 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1303255 m) (@lem1303254 m)). Qed.
Lemma lem1303257 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1303256 m p). Qed.
Lemma lem1303258 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1303260 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303261 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1303260 h1 m). Qed.
Lemma lem1303262 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1303263 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1303262 m) (@lem1303261 m h1)). Qed.
Lemma lem1303264 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1303263 m h1 n). Qed.
Lemma lem1303265 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1303266 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1303265 n m) (@lem1303264 m n h1)). Qed.
Lemma lem1303267 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1303266 n m h1 p). Qed.
Lemma lem1303268 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1303269 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1303268 n m p) (@lem1303267 n m p h1)). Qed.
Lemma lem1303270 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1303271 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1303269 n m p h1 (@lem1303270 m n p h2)). Qed.
Lemma lem1303272 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1303271 m n p h0 h1). Qed.
Lemma lem1303273 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1303274 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1303273 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1303272 m n p h0)). Qed.
Lemma lem1303275 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303276 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1303274 m p h2 (@lem1303275 h1)). Qed.
Lemma lem1303277 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1303276 m p h1 h0). Qed.
Lemma lem1303278 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1303277 m p h1). Qed.
Lemma lem1303279 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1303278 m h1). Qed.
Lemma lem1303280 : term14.
Proof. exact (fun h0 : term0 => @lem1303279 h0). Qed.
Lemma lem1303281 : term13.
Proof. exact (@lem1303280 (@lem93743)). Qed.
Lemma lem1303282 (m : nat) : term15 m.
Proof. exact (@lem1303281 m). Qed.
Lemma lem1303283 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1303284 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1303283 m) (@lem1303282 m)). Qed.
Lemma lem1303285 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1303284 m p). Qed.
Lemma lem1303286 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1303288 (x : nadd) : term92 x.
Proof. exact (@lem1299579 x). Qed.
Lemma lem1303289 (x : nadd) : (term92 x) = (term93 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1303290 (x : nadd) : term93 x.
Proof. exact (EQ_MP (@lem1303289 x) (@lem1303288 x)). Qed.
Lemma lem1303291 (x : nadd) (B2 : nat) (h1 : term94 x B2) : term94 x B2.
Proof. exact (h1). Qed.
Lemma lem1303292 (x : nadd) : term95 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1303293 (x : nadd) : (term95 x) = (term96 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1303294 (x : nadd) : term96 x.
Proof. exact (EQ_MP (@lem1303293 x) (@lem1303292 x)). Qed.
Lemma lem1303295 (x : nadd) (B1 : nat) (h1 : term97 x B1) : term97 x B1.
Proof. exact (h1). Qed.
Lemma lem1303296 (x : nadd) : term98 x.
Proof. exact (@lem1302948 x). Qed.
Lemma lem1303297 (x : nadd) : (term98 x) = (term99 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1303299 (x : nadd) (h1 : term100 x) : term100 x.
Proof. exact (h1). Qed.
Lemma lem1303301 (x : nadd) : term99 x.
Proof. exact (EQ_MP (@lem1303297 x) (@lem1303296 x)). Qed.
Lemma lem1303302 (x : nadd) (h1 : term100 x) : term101 x.
Proof. exact (@lem1303301 x (@lem1303299 x h1)). Qed.
Lemma lem1303303 (x : nadd) (h1 : term101 x) : term101 x.
Proof. exact (h1). Qed.
Lemma lem1303304 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term102 N1 x.
Proof. exact (h1). Qed.
Lemma lem1303305 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (h1). Qed.
Lemma lem1303306 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term104 m N1 N2 n) : term104 m N1 N2 n.
Proof. exact (h1). Qed.
Lemma lem1303307 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : term105 N1 N2 n.
Proof. exact (h1). Qed.
Lemma lem1303308 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : term105 N1 N2 m.
Proof. exact (h1). Qed.
Lemma lem1303310 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303286 m p) (@lem1303285 m p)). Qed.
Lemma lem1303311 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : term106 x B1 B2 m n.
Proof. exact (@lem1303310 (term107 n x m) (term108 B1 B2 m n)). Qed.
Lemma lem1303330 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term102 N1 x.
Proof. exact (h1). Qed.
Lemma lem1303331 (m : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term109 N1 x m.
Proof. exact (@lem1303330 N1 x h1 m). Qed.
Lemma lem1303332 (N1 : nat) (x : nadd) (m : nat) : (term109 N1 x m) = (term110 N1 x m).
Proof. exact (eq_refl (term109 N1 x m)). Qed.
Lemma lem1303333 (m : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term110 N1 x m.
Proof. exact (EQ_MP (@lem1303332 N1 x m) (@lem1303331 m N1 x h1)). Qed.
Lemma lem1303334 (m : nat) (n : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term111 N1 x m n.
Proof. exact (@lem1303333 m N1 x h1 n). Qed.
Lemma lem1303335 (N1 : nat) (x : nadd) (m : nat) (n : nat) : (term111 N1 x m n) = (term112 N1 x m n).
Proof. exact (eq_refl (term111 N1 x m n)). Qed.
Lemma lem1303336 (m : nat) (n : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term112 N1 x m n.
Proof. exact (EQ_MP (@lem1303335 N1 x m n) (@lem1303334 m n N1 x h1)). Qed.
Lemma lem1303337 (m : nat) (N1 : nat) (n : nat) (h1 : term113 m N1 n) : term113 m N1 n.
Proof. exact (h1). Qed.
Lemma lem1303338 (x : nadd) (m : nat) (N1 : nat) (n : nat) (h1 : term102 N1 x) (h2 : term113 m N1 n) : term114 x m n.
Proof. exact (@lem1303336 m n N1 x h1 (@lem1303337 m N1 n h2)). Qed.
Lemma lem1303339 (x : nadd) (m : nat) (N1 : nat) (n : nat) (h1 : term113 m N1 n) : term115 N1 x m n.
Proof. exact (fun h0 : term102 N1 x => @lem1303338 x m N1 n h0 h1). Qed.
Lemma lem1303340 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term102 N1 x.
Proof. exact (h1). Qed.
Lemma lem1303341 (x : nadd) (m : nat) (N1 : nat) (n : nat) (h1 : term102 N1 x) (h2 : term113 m N1 n) : term114 x m n.
Proof. exact (@lem1303339 x m N1 n h2 (@lem1303340 N1 x h1)). Qed.
Lemma lem1303342 (m : nat) (n : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term112 N1 x m n.
Proof. exact (fun h0 : term113 m N1 n => @lem1303341 x m N1 n h1 h0). Qed.
Lemma lem1303343 (m : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term110 N1 x m.
Proof. exact (fun n : nat => @lem1303342 m n N1 x h1). Qed.
Lemma lem1303344 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term102 N1 x.
Proof. exact (fun m : nat => @lem1303343 m N1 x h1). Qed.
Lemma lem1303345 (N1 : nat) (x : nadd) : term116 N1 x.
Proof. exact (fun h0 : term102 N1 x => @lem1303344 N1 x h0). Qed.
Lemma lem1303346 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term102 N1 x.
Proof. exact (@lem1303345 N1 x (@lem1303304 N1 x h1)). Qed.
Lemma lem1303347 (m : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term109 N1 x m.
Proof. exact (@lem1303346 N1 x h1 m). Qed.
Lemma lem1303348 (N1 : nat) (x : nadd) (m : nat) : (term109 N1 x m) = (term110 N1 x m).
Proof. exact (eq_refl (term109 N1 x m)). Qed.
Lemma lem1303349 (m : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term110 N1 x m.
Proof. exact (EQ_MP (@lem1303348 N1 x m) (@lem1303347 m N1 x h1)). Qed.
Lemma lem1303350 (m : nat) (n : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term111 N1 x m n.
Proof. exact (@lem1303349 m N1 x h1 n). Qed.
Lemma lem1303351 (N1 : nat) (x : nadd) (m : nat) (n : nat) : (term111 N1 x m n) = (term112 N1 x m n).
Proof. exact (eq_refl (term111 N1 x m n)). Qed.
Lemma lem1303354 (m : nat) (n : nat) (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term112 N1 x m n.
Proof. exact (EQ_MP (@lem1303351 N1 x m n) (@lem1303350 m n N1 x h1)). Qed.
Lemma lem1303356 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303258 m p) (@lem1303257 m p)). Qed.
Lemma lem1303357 (N1 : nat) (m : nat) : term11 N1 m.
Proof. exact (@lem1303356 N1 m). Qed.
Lemma lem1303359 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303258 m p) (@lem1303257 m p)). Qed.
Lemma lem1303360 (N1 : nat) (n : nat) : term11 N1 n.
Proof. exact (@lem1303359 N1 n). Qed.
Lemma lem1303369 (m : nat) : term117 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1303370 (m : nat) : (term117 m) = (term118 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem1303371 (m : nat) : term118 m.
Proof. exact (EQ_MP (@lem1303370 m) (@lem1303369 m)). Qed.
Lemma lem1303372 (m : nat) (n : nat) : term119 m n.
Proof. exact (@lem1303371 m n). Qed.
Lemma lem1303373 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem1303374 (m : nat) (n : nat) : term120 m n.
Proof. exact (EQ_MP (@lem1303373 m n) (@lem1303372 m n)). Qed.
Lemma lem1303375 (m : nat) (n : nat) : (term120 m n) = ((term120 m n) = True).
Proof. exact (@lem7 (term120 m n)). Qed.
Lemma lem1303398 (N1 : nat) (N2 : nat) (m : nat) : (term105 N1 N2 m) = ((term105 N1 N2 m) = True).
Proof. exact (@lem7 (term105 N1 N2 m)). Qed.
Lemma lem1303407 (m : nat) (n : nat) : (term120 m n) = True.
Proof. exact (EQ_MP (@lem1303375 m n) (@lem1303374 m n)). Qed.
Lemma lem1303408 (N1 : nat) (N2 : nat) : (term120 N1 N2) = True.
Proof. exact (@lem1303407 N1 N2). Qed.
Lemma lem1303409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1303410 (N1 : nat) (N2 : nat) : (term121 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1303409) (@lem1303408 N1 N2)). Qed.
Lemma lem1303412 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term105 N1 N2 m) = True.
Proof. exact (EQ_MP (@lem1303398 N1 N2 m) (@lem1303308 N1 N2 m h1)). Qed.
Lemma lem1303413 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term122 N1 N2 m) = (True /\ True).
Proof. exact (MK_COMB (@lem1303410 N1 N2) (@lem1303412 N1 N2 m h1)). Qed.
Lemma lem1303415 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1303416 : (True /\ True) = True.
Proof. exact (@lem1303415 True). Qed.
Lemma lem1303417 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term122 N1 N2 m) = True.
Proof. exact (TRANS (@lem1303413 N1 N2 m h1) (@lem1303416)). Qed.
Lemma lem1303418 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : True = (term122 N1 N2 m).
Proof. exact (SYM (@lem1303417 N1 N2 m h1)). Qed.
Lemma lem1303419 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : term122 N1 N2 m.
Proof. exact (EQ_MP (@lem1303418 N1 N2 m h1) (@lem0)). Qed.
Lemma lem1303428 (m : nat) : term117 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1303429 (m : nat) : (term117 m) = (term118 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem1303430 (m : nat) : term118 m.
Proof. exact (EQ_MP (@lem1303429 m) (@lem1303428 m)). Qed.
Lemma lem1303431 (m : nat) (n : nat) : term119 m n.
Proof. exact (@lem1303430 m n). Qed.
Lemma lem1303432 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (eq_refl (term119 m n)). Qed.
Lemma lem1303433 (m : nat) (n : nat) : term120 m n.
Proof. exact (EQ_MP (@lem1303432 m n) (@lem1303431 m n)). Qed.
Lemma lem1303434 (m : nat) (n : nat) : (term120 m n) = ((term120 m n) = True).
Proof. exact (@lem7 (term120 m n)). Qed.
Lemma lem1303459 (N1 : nat) (N2 : nat) (n : nat) : (term105 N1 N2 n) = ((term105 N1 N2 n) = True).
Proof. exact (@lem7 (term105 N1 N2 n)). Qed.
Lemma lem1303466 (m : nat) (n : nat) : (term120 m n) = True.
Proof. exact (EQ_MP (@lem1303434 m n) (@lem1303433 m n)). Qed.
Lemma lem1303467 (N1 : nat) (N2 : nat) : (term120 N1 N2) = True.
Proof. exact (@lem1303466 N1 N2). Qed.
Lemma lem1303468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1303469 (N1 : nat) (N2 : nat) : (term121 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1303468) (@lem1303467 N1 N2)). Qed.
Lemma lem1303471 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term105 N1 N2 n) = True.
Proof. exact (EQ_MP (@lem1303459 N1 N2 n) (@lem1303307 N1 N2 n h1)). Qed.
Lemma lem1303472 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term122 N1 N2 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1303469 N1 N2) (@lem1303471 N1 N2 n h1)). Qed.
Lemma lem1303474 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1303475 : (True /\ True) = True.
Proof. exact (@lem1303474 True). Qed.
Lemma lem1303476 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term122 N1 N2 n) = True.
Proof. exact (TRANS (@lem1303472 N1 N2 n h1) (@lem1303475)). Qed.
Lemma lem1303477 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : True = (term122 N1 N2 n).
Proof. exact (SYM (@lem1303476 N1 N2 n h1)). Qed.
Lemma lem1303478 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : term122 N1 N2 n.
Proof. exact (EQ_MP (@lem1303477 N1 N2 n h1) (@lem0)). Qed.
Lemma lem1303479 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : term9 N1 n.
Proof. exact (ex_intro (term10 N1 n) (Nat.add N1 N2) (@lem1303478 N1 N2 n h1)). Qed.
Lemma lem1303480 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : term9 N1 m.
Proof. exact (ex_intro (term10 N1 m) (Nat.add N1 N2) (@lem1303419 N1 N2 m h1)). Qed.
Lemma lem1303481 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : Peano.le N1 n.
Proof. exact (@lem1303360 N1 n (@lem1303479 N1 N2 n h1)). Qed.
Lemma lem1303482 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : Peano.le N1 m.
Proof. exact (@lem1303357 N1 m (@lem1303480 N1 N2 m h1)). Qed.
Lemma lem1303483 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 m) (h2 : term105 N1 N2 n) : term113 m N1 n.
Proof. exact (conj (@lem1303482 N1 N2 m h1) (@lem1303481 N1 N2 n h2)). Qed.
Lemma lem1303484 (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term102 N1 x) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term114 x m n.
Proof. exact (@lem1303354 m n N1 x h1 (@lem1303483 m N1 N2 n h2 h3)). Qed.
Lemma lem1303486 (m : nat) (n : nat) (p : nat) : (term90 m n p) = (term91 m n p).
Proof. exact (EQ_MP (@lem1303230 m n p) (@lem1303229 m n p)). Qed.
Lemma lem1303487 (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term108 B1 B2 m n) = (term123 B1 B2 m n).
Proof. exact (@lem1303486 B1 (Nat.mul B2 B2) (term124 m n)). Qed.
Lemma lem1303488 (x : nadd) (m : nat) (n : nat) : (term125 x m n) = (term125 x m n).
Proof. exact (eq_refl (term125 x m n)). Qed.
Lemma lem1303489 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term126 x B1 B2 m n) = (term127 x B1 B2 m n).
Proof. exact (MK_COMB (@lem1303488 x m n) (@lem1303487 B1 B2 m n)). Qed.
Lemma lem1303490 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term127 x B1 B2 m n) = (term126 x B1 B2 m n).
Proof. exact (SYM (@lem1303489 x B1 B2 m n)). Qed.
Lemma lem1303492 (m : nat) (n : nat) (p : nat) (q : nat) : term81 m n p q.
Proof. exact (EQ_MP (@lem1303221 m n p q) (@lem1303220 m n p q)). Qed.
Lemma lem1303493 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : term128 x B1 B2 m n.
Proof. exact (@lem1303492 (term129 n x m) (term130 x m n) (term131 B1 m n) (term132 B2 m n)). Qed.
Lemma lem1303495 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1303184 n m) (@lem1303183 m n)). Qed.
Lemma lem1303496 (m : nat) (n : nat) (B1 : nat) : (term131 B1 m n) = (term133 m n B1).
Proof. exact (@lem1303495 (term124 m n) B1). Qed.
Lemma lem1303497 (n : nat) (x : nadd) (m : nat) : (term134 n x m) = (term134 n x m).
Proof. exact (eq_refl (term134 n x m)). Qed.
Lemma lem1303498 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term135 x B1 m n) = (term136 x m n B1).
Proof. exact (MK_COMB (@lem1303497 n x m) (@lem1303496 m n B1)). Qed.
Lemma lem1303499 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term136 x m n B1) = (term135 x B1 m n).
Proof. exact (SYM (@lem1303498 x m n B1)). Qed.
Lemma lem1303501 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (term46 m n p).
Proof. exact (EQ_MP (@lem1303178 m n p) (@lem1303177 m n p)). Qed.
Lemma lem1303502 (m : nat) (n : nat) (B1 : nat) : (term133 m n B1) = (term137 m n B1).
Proof. exact (@lem1303501 (Nat.mul m n) (Nat.add m n) B1). Qed.
Lemma lem1303503 (n : nat) (x : nadd) (m : nat) : (term134 n x m) = (term134 n x m).
Proof. exact (eq_refl (term134 n x m)). Qed.
Lemma lem1303504 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term136 x m n B1) = (term138 x m n B1).
Proof. exact (MK_COMB (@lem1303503 n x m) (@lem1303502 m n B1)). Qed.
Lemma lem1303505 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term138 x m n B1) = (term136 x m n B1).
Proof. exact (SYM (@lem1303504 x m n B1)). Qed.
Lemma lem1303507 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1303151 n m) (@lem1303150 m n)). Qed.
Lemma lem1303508 (B1 : nat) (m : nat) (n : nat) : (term90 m n B1) = (term139 B1 m n).
Proof. exact (@lem1303507 B1 (Nat.add m n)). Qed.
Lemma lem1303509 (m : nat) (n : nat) : (term140 m n) = (term140 m n).
Proof. exact (eq_refl (term140 m n)). Qed.
Lemma lem1303510 (B1 : nat) (m : nat) (n : nat) : (term137 m n B1) = (term141 B1 m n).
Proof. exact (MK_COMB (@lem1303509 m n) (@lem1303508 B1 m n)). Qed.
Lemma lem1303511 (n : nat) (x : nadd) (m : nat) : (term134 n x m) = (term134 n x m).
Proof. exact (eq_refl (term134 n x m)). Qed.
Lemma lem1303512 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term138 x m n B1) = (term142 x B1 m n).
Proof. exact (MK_COMB (@lem1303511 n x m) (@lem1303510 B1 m n)). Qed.
Lemma lem1303513 (x : nadd) (m : nat) (n : nat) (B1 : nat) : (term142 x B1 m n) = (term138 x m n B1).
Proof. exact (SYM (@lem1303512 x B1 m n)). Qed.
Lemma lem1303514 (m : nat) : term143 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1303515 (m : nat) : (term143 m) = (term144 m).
Proof. exact (eq_refl (term143 m)). Qed.
Lemma lem1303516 (m : nat) : term144 m.
Proof. exact (EQ_MP (@lem1303515 m) (@lem1303514 m)). Qed.
Lemma lem1303517 (m : nat) (n : nat) : term145 m n.
Proof. exact (@lem1303516 m n). Qed.
Lemma lem1303518 (m : nat) (n : nat) : (term145 m n) = (term146 m n).
Proof. exact (eq_refl (term145 m n)). Qed.
Lemma lem1303519 (m : nat) (n : nat) : term146 m n.
Proof. exact (EQ_MP (@lem1303518 m n) (@lem1303517 m n)). Qed.
Lemma lem1303520 (m : nat) (n : nat) (p : nat) : term147 m n p.
Proof. exact (@lem1303519 m n p). Qed.
Lemma lem1303521 (m : nat) (n : nat) (p : nat) : (term147 m n p) = ((term148 n m p) = (term149 m n p)).
Proof. exact (eq_refl (term147 m n p)). Qed.
Lemma lem1303531 (m : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term150 x B1 m.
Proof. exact (@lem1303295 x B1 h1 m). Qed.
Lemma lem1303532 (x : nadd) (B1 : nat) (m : nat) : (term150 x B1 m) = (term151 x B1 m).
Proof. exact (eq_refl (term150 x B1 m)). Qed.
Lemma lem1303533 (m : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term151 x B1 m.
Proof. exact (EQ_MP (@lem1303532 x B1 m) (@lem1303531 m x B1 h1)). Qed.
Lemma lem1303534 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term152 x B1 m n.
Proof. exact (@lem1303533 m x B1 h1 n). Qed.
Lemma lem1303535 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term152 x B1 m n) = (term153 x B1 m n).
Proof. exact (eq_refl (term152 x B1 m n)). Qed.
Lemma lem1303536 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term153 x B1 m n.
Proof. exact (EQ_MP (@lem1303535 x B1 m n) (@lem1303534 m n x B1 h1)). Qed.
Lemma lem1303537 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term153 x B1 m n) = ((term153 x B1 m n) = True).
Proof. exact (@lem7 (term153 x B1 m n)). Qed.
Lemma lem1303549 (m : nat) (n : nat) (p : nat) : (term148 n m p) = (term149 m n p).
Proof. exact (EQ_MP (@lem1303521 m n p) (@lem1303520 m n p)). Qed.
Lemma lem1303550 (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term142 x B1 m n) = (term154 x B1 m n).
Proof. exact (@lem1303549 (Nat.mul m n) (term155 n x m) (term139 B1 m n)). Qed.
Lemma lem1303556 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : (term153 x B1 m n) = True.
Proof. exact (EQ_MP (@lem1303537 x B1 m n) (@lem1303536 m n x B1 h1)). Qed.
Lemma lem1303557 (m : nat) (n : nat) : (term156 m n) = (term156 m n).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem1303558 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : (term154 x B1 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem1303557 m n) (@lem1303556 m n x B1 h1)). Qed.
Lemma lem1303560 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1303561 (m : nat) (n : nat) : (term157 m n) = True.
Proof. exact (@lem1303560 ((Nat.mul m n) = (NUMERAL 0))). Qed.
Lemma lem1303562 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : (term154 x B1 m n) = True.
Proof. exact (TRANS (@lem1303558 m n x B1 h1) (@lem1303561 m n)). Qed.
Lemma lem1303563 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : (term142 x B1 m n) = True.
Proof. exact (TRANS (@lem1303550 x B1 m n) (@lem1303562 m n x B1 h1)). Qed.
Lemma lem1303564 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : True = (term142 x B1 m n).
Proof. exact (SYM (@lem1303563 m n x B1 h1)). Qed.
Lemma lem1303565 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term142 x B1 m n.
Proof. exact (EQ_MP (@lem1303564 m n x B1 h1) (@lem0)). Qed.
Lemma lem1303566 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term138 x m n B1.
Proof. exact (EQ_MP (@lem1303513 x m n B1) (@lem1303565 m n x B1 h1)). Qed.
Lemma lem1303567 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term136 x m n B1.
Proof. exact (EQ_MP (@lem1303505 x m n B1) (@lem1303566 m n x B1 h1)). Qed.
Lemma lem1303568 (m : nat) (n : nat) (x : nadd) (B1 : nat) (h1 : term97 x B1) : term135 x B1 m n.
Proof. exact (EQ_MP (@lem1303499 x B1 m n) (@lem1303567 m n x B1 h1)). Qed.
Lemma lem1303570 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : (term47 a b c d e) = (term54 a c b d e).
Proof. exact (EQ_MP (@lem1303145 a c b d e) (@lem0)). Qed.
Lemma lem1303571 (B2 : nat) (m : nat) (n : nat) : (term132 B2 m n) = (term158 B2 m n).
Proof. exact (@lem1303570 B2 m B2 n (Nat.add m n)). Qed.
Lemma lem1303572 (x : nadd) (m : nat) (n : nat) : (term159 x m n) = (term159 x m n).
Proof. exact (eq_refl (term159 x m n)). Qed.
Lemma lem1303573 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term160 x B2 m n) = (term161 x B2 m n).
Proof. exact (MK_COMB (@lem1303572 x m n) (@lem1303571 B2 m n)). Qed.
Lemma lem1303574 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term161 x B2 m n) = (term160 x B2 m n).
Proof. exact (SYM (@lem1303573 x B2 m n)). Qed.
Lemma lem1303576 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (term42 m n p).
Proof. exact (EQ_MP (@lem1303021 m n p) (@lem1303020 m n p)). Qed.
Lemma lem1303577 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term161 x B2 m n) = (term162 x B2 m n).
Proof. exact (@lem1303576 (term163 m x n) (term164 m B2 n) (Nat.add m n)). Qed.
Lemma lem1303584 (x : nadd) (B2 : nat) (m : nat) (n : nat) : (term162 x B2 m n) = (term161 x B2 m n).
Proof. exact (SYM (@lem1303577 x B2 m n)). Qed.
Lemma lem1303586 (m : nat) (p : nat) (n : nat) (q : nat) : term25 m p n q.
Proof. exact (EQ_MP (@lem1303012 m p n q) (@lem1303011 m p n q)). Qed.
Lemma lem1303587 (x : nadd) (m : nat) (B2 : nat) (n : nat) : term165 x m B2 n.
Proof. exact (@lem1303586 (dest_nadd x m) (dest_nadd x n) (Nat.mul B2 m) (Nat.mul B2 n)). Qed.
Lemma lem1303588 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (h1). Qed.
Lemma lem1303589 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term166 N2 x B2 n.
Proof. exact (@lem1303588 N2 x B2 h1 n). Qed.
Lemma lem1303590 (N2 : nat) (x : nadd) (B2 : nat) (n : nat) : (term166 N2 x B2 n) = (term167 N2 x B2 n).
Proof. exact (eq_refl (term166 N2 x B2 n)). Qed.
Lemma lem1303591 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (EQ_MP (@lem1303590 N2 x B2 n) (@lem1303589 n N2 x B2 h1)). Qed.
Lemma lem1303592 (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : Peano.le N2 n.
Proof. exact (h1). Qed.
Lemma lem1303593 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : Peano.le N2 n) : term168 x B2 n.
Proof. exact (@lem1303591 n N2 x B2 h1 (@lem1303592 N2 n h2)). Qed.
Lemma lem1303594 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : term169 N2 x B2 n.
Proof. exact (fun h0 : term103 N2 x B2 => @lem1303593 x B2 N2 n h0 h1). Qed.
Lemma lem1303595 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (h1). Qed.
Lemma lem1303596 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : Peano.le N2 n) : term168 x B2 n.
Proof. exact (@lem1303594 x B2 N2 n h2 (@lem1303595 N2 x B2 h1)). Qed.
Lemma lem1303597 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (fun h0 : Peano.le N2 n => @lem1303596 x B2 N2 n h1 h0). Qed.
Lemma lem1303598 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (fun n : nat => @lem1303597 n N2 x B2 h1). Qed.
Lemma lem1303599 (N2 : nat) (x : nadd) (B2 : nat) : term170 N2 x B2.
Proof. exact (fun h0 : term103 N2 x B2 => @lem1303598 N2 x B2 h0). Qed.
Lemma lem1303600 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (@lem1303599 N2 x B2 (@lem1303305 N2 x B2 h1)). Qed.
Lemma lem1303601 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term166 N2 x B2 n.
Proof. exact (@lem1303600 N2 x B2 h1 n). Qed.
Lemma lem1303602 (N2 : nat) (x : nadd) (B2 : nat) (n : nat) : (term166 N2 x B2 n) = (term167 N2 x B2 n).
Proof. exact (eq_refl (term166 N2 x B2 n)). Qed.
Lemma lem1303605 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (EQ_MP (@lem1303602 N2 x B2 n) (@lem1303601 n N2 x B2 h1)). Qed.
Lemma lem1303606 (m : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 m.
Proof. exact (@lem1303605 m N2 x B2 h1). Qed.
Lemma lem1303607 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (h1). Qed.
Lemma lem1303608 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term166 N2 x B2 n.
Proof. exact (@lem1303607 N2 x B2 h1 n). Qed.
Lemma lem1303609 (N2 : nat) (x : nadd) (B2 : nat) (n : nat) : (term166 N2 x B2 n) = (term167 N2 x B2 n).
Proof. exact (eq_refl (term166 N2 x B2 n)). Qed.
Lemma lem1303610 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (EQ_MP (@lem1303609 N2 x B2 n) (@lem1303608 n N2 x B2 h1)). Qed.
Lemma lem1303611 (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : Peano.le N2 n.
Proof. exact (h1). Qed.
Lemma lem1303612 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : Peano.le N2 n) : term168 x B2 n.
Proof. exact (@lem1303610 n N2 x B2 h1 (@lem1303611 N2 n h2)). Qed.
Lemma lem1303613 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : term169 N2 x B2 n.
Proof. exact (fun h0 : term103 N2 x B2 => @lem1303612 x B2 N2 n h0 h1). Qed.
Lemma lem1303614 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (h1). Qed.
Lemma lem1303615 (x : nadd) (B2 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : Peano.le N2 n) : term168 x B2 n.
Proof. exact (@lem1303613 x B2 N2 n h2 (@lem1303614 N2 x B2 h1)). Qed.
Lemma lem1303616 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (fun h0 : Peano.le N2 n => @lem1303615 x B2 N2 n h1 h0). Qed.
Lemma lem1303617 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (fun n : nat => @lem1303616 n N2 x B2 h1). Qed.
Lemma lem1303618 (N2 : nat) (x : nadd) (B2 : nat) : term170 N2 x B2.
Proof. exact (fun h0 : term103 N2 x B2 => @lem1303617 N2 x B2 h0). Qed.
Lemma lem1303619 (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term103 N2 x B2.
Proof. exact (@lem1303618 N2 x B2 (@lem1303305 N2 x B2 h1)). Qed.
Lemma lem1303620 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term166 N2 x B2 n.
Proof. exact (@lem1303619 N2 x B2 h1 n). Qed.
Lemma lem1303621 (N2 : nat) (x : nadd) (B2 : nat) (n : nat) : (term166 N2 x B2 n) = (term167 N2 x B2 n).
Proof. exact (eq_refl (term166 N2 x B2 n)). Qed.
Lemma lem1303624 (n : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term103 N2 x B2) : term167 N2 x B2 n.
Proof. exact (EQ_MP (@lem1303621 N2 x B2 n) (@lem1303620 n N2 x B2 h1)). Qed.
Lemma lem1303626 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1302975 m p) (@lem1302974 m p)). Qed.
Lemma lem1303627 (N2 : nat) (m : nat) : term11 N2 m.
Proof. exact (@lem1303626 N2 m). Qed.
Lemma lem1303629 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1302975 m p) (@lem1302974 m p)). Qed.
Lemma lem1303630 (N2 : nat) (n : nat) : term11 N2 n.
Proof. exact (@lem1303629 N2 n). Qed.
Lemma lem1303631 (m : nat) : term171 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1303632 (m : nat) : (term171 m) = (term172 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem1303633 (m : nat) : term172 m.
Proof. exact (EQ_MP (@lem1303632 m) (@lem1303631 m)). Qed.
Lemma lem1303634 (m : nat) (n : nat) : term173 m n.
Proof. exact (@lem1303633 m n). Qed.
Lemma lem1303635 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem1303636 (m : nat) (n : nat) : term174 m n.
Proof. exact (EQ_MP (@lem1303635 m n) (@lem1303634 m n)). Qed.
Lemma lem1303637 (m : nat) (n : nat) : (term174 m n) = ((term174 m n) = True).
Proof. exact (@lem7 (term174 m n)). Qed.
Lemma lem1303668 (N1 : nat) (N2 : nat) (m : nat) : (term105 N1 N2 m) = ((term105 N1 N2 m) = True).
Proof. exact (@lem7 (term105 N1 N2 m)). Qed.
Lemma lem1303675 (m : nat) (n : nat) : (term174 m n) = True.
Proof. exact (EQ_MP (@lem1303637 m n) (@lem1303636 m n)). Qed.
Lemma lem1303676 (N1 : nat) (N2 : nat) : (term174 N1 N2) = True.
Proof. exact (@lem1303675 N1 N2). Qed.
Lemma lem1303677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1303678 (N1 : nat) (N2 : nat) : (term175 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1303677) (@lem1303676 N1 N2)). Qed.
Lemma lem1303680 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term105 N1 N2 m) = True.
Proof. exact (EQ_MP (@lem1303668 N1 N2 m) (@lem1303308 N1 N2 m h1)). Qed.
Lemma lem1303681 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term176 N1 N2 m) = (True /\ True).
Proof. exact (MK_COMB (@lem1303678 N1 N2) (@lem1303680 N1 N2 m h1)). Qed.
Lemma lem1303683 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1303684 : (True /\ True) = True.
Proof. exact (@lem1303683 True). Qed.
Lemma lem1303685 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : (term176 N1 N2 m) = True.
Proof. exact (TRANS (@lem1303681 N1 N2 m h1) (@lem1303684)). Qed.
Lemma lem1303686 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : True = (term176 N1 N2 m).
Proof. exact (SYM (@lem1303685 N1 N2 m h1)). Qed.
Lemma lem1303687 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : term176 N1 N2 m.
Proof. exact (EQ_MP (@lem1303686 N1 N2 m h1) (@lem0)). Qed.
Lemma lem1303688 (m : nat) : term171 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1303689 (m : nat) : (term171 m) = (term172 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem1303690 (m : nat) : term172 m.
Proof. exact (EQ_MP (@lem1303689 m) (@lem1303688 m)). Qed.
Lemma lem1303691 (m : nat) (n : nat) : term173 m n.
Proof. exact (@lem1303690 m n). Qed.
Lemma lem1303692 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem1303693 (m : nat) (n : nat) : term174 m n.
Proof. exact (EQ_MP (@lem1303692 m n) (@lem1303691 m n)). Qed.
Lemma lem1303694 (m : nat) (n : nat) : (term174 m n) = ((term174 m n) = True).
Proof. exact (@lem7 (term174 m n)). Qed.
Lemma lem1303727 (N1 : nat) (N2 : nat) (n : nat) : (term105 N1 N2 n) = ((term105 N1 N2 n) = True).
Proof. exact (@lem7 (term105 N1 N2 n)). Qed.
Lemma lem1303732 (m : nat) (n : nat) : (term174 m n) = True.
Proof. exact (EQ_MP (@lem1303694 m n) (@lem1303693 m n)). Qed.
Lemma lem1303733 (N1 : nat) (N2 : nat) : (term174 N1 N2) = True.
Proof. exact (@lem1303732 N1 N2). Qed.
Lemma lem1303734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1303735 (N1 : nat) (N2 : nat) : (term175 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1303734) (@lem1303733 N1 N2)). Qed.
Lemma lem1303737 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term105 N1 N2 n) = True.
Proof. exact (EQ_MP (@lem1303727 N1 N2 n) (@lem1303307 N1 N2 n h1)). Qed.
Lemma lem1303738 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term176 N1 N2 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1303735 N1 N2) (@lem1303737 N1 N2 n h1)). Qed.
Lemma lem1303740 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1303741 : (True /\ True) = True.
Proof. exact (@lem1303740 True). Qed.
Lemma lem1303742 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : (term176 N1 N2 n) = True.
Proof. exact (TRANS (@lem1303738 N1 N2 n h1) (@lem1303741)). Qed.
Lemma lem1303743 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : True = (term176 N1 N2 n).
Proof. exact (SYM (@lem1303742 N1 N2 n h1)). Qed.
Lemma lem1303744 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : term176 N1 N2 n.
Proof. exact (EQ_MP (@lem1303743 N1 N2 n h1) (@lem0)). Qed.
Lemma lem1303745 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : term9 N2 n.
Proof. exact (ex_intro (term10 N2 n) (Nat.add N1 N2) (@lem1303744 N1 N2 n h1)). Qed.
Lemma lem1303746 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : term9 N2 m.
Proof. exact (ex_intro (term10 N2 m) (Nat.add N1 N2) (@lem1303687 N1 N2 m h1)). Qed.
Lemma lem1303747 (N1 : nat) (N2 : nat) (n : nat) (h1 : term105 N1 N2 n) : Peano.le N2 n.
Proof. exact (@lem1303630 N2 n (@lem1303745 N1 N2 n h1)). Qed.
Lemma lem1303748 (N1 : nat) (N2 : nat) (m : nat) (h1 : term105 N1 N2 m) : Peano.le N2 m.
Proof. exact (@lem1303627 N2 m (@lem1303746 N1 N2 m h1)). Qed.
Lemma lem1303749 (x : nadd) (B2 : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 n) : term168 x B2 n.
Proof. exact (@lem1303624 n N2 x B2 h1 (@lem1303747 N1 N2 n h2)). Qed.
Lemma lem1303750 (x : nadd) (B2 : nat) (N1 : nat) (N2 : nat) (m : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) : term168 x B2 m.
Proof. exact (@lem1303606 m N2 x B2 h1 (@lem1303748 N1 N2 m h2)). Qed.
Lemma lem1303751 (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term177 m x B2 n.
Proof. exact (conj (@lem1303750 x B2 N1 N2 m h1 h2) (@lem1303749 x B2 N1 N2 n h1 h3)). Qed.
Lemma lem1303752 (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term178 x m B2 n.
Proof. exact (@lem1303587 x m B2 n (@lem1303751 x B2 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1303753 (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term162 x B2 m n.
Proof. exact (or_intro1 (@lem1303752 x B2 m N1 N2 n h1 h2 h3) ((Nat.add m n) = (NUMERAL 0))). Qed.
Lemma lem1303754 (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term161 x B2 m n.
Proof. exact (EQ_MP (@lem1303584 x B2 m n) (@lem1303753 x B2 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1303755 (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term103 N2 x B2) (h2 : term105 N1 N2 m) (h3 : term105 N1 N2 n) : term160 x B2 m n.
Proof. exact (EQ_MP (@lem1303574 x B2 m n) (@lem1303754 x B2 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1303756 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term103 N2 x B2) (h3 : term105 N1 N2 m) (h4 : term105 N1 N2 n) : term179 B1 x B2 m n.
Proof. exact (conj (@lem1303568 m n x B1 h1) (@lem1303755 x B2 m N1 N2 n h2 h3 h4)). Qed.
Lemma lem1303757 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term103 N2 x B2) (h3 : term105 N1 N2 m) (h4 : term105 N1 N2 n) : term127 x B1 B2 m n.
Proof. exact (@lem1303493 x B1 B2 m n (@lem1303756 B1 x B2 m N1 N2 n h1 h2 h3 h4)). Qed.
Lemma lem1303758 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term103 N2 x B2) (h3 : term105 N1 N2 m) (h4 : term105 N1 N2 n) : term126 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1303490 x B1 B2 m n) (@lem1303757 B1 x B2 m N1 N2 n h1 h2 h3 h4)). Qed.
Lemma lem1303759 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : term180 x B1 B2 m n.
Proof. exact (conj (@lem1303484 x m N1 N2 n h2 h4 h5) (@lem1303758 B1 x B2 m N1 N2 n h1 h3 h4 h5)). Qed.
Lemma lem1303760 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : term181 x B1 B2 m n.
Proof. exact (ex_intro (term182 x B1 B2 m n) (term183 x m n) (@lem1303759 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5)). Qed.
Lemma lem1303761 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : term184 x B1 B2 m n.
Proof. exact (@lem1303311 x B1 B2 m n (@lem1303760 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5)). Qed.
Lemma lem1303762 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term104 m N1 N2 n) : term105 N1 N2 n.
Proof. exact (proj2 (@lem1303306 m N1 N2 n h1)). Qed.
Lemma lem1303763 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term104 m N1 N2 n) : term105 N1 N2 m.
Proof. exact (proj1 (@lem1303306 m N1 N2 n h1)). Qed.
Lemma lem1303764 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : (term105 N1 N2 n) = (term184 x B1 B2 m n).
Proof. exact (prop_ext (fun h6 : term105 N1 N2 n => @lem1303761 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5) (fun h6 : term184 x B1 B2 m n => @lem1303307 N1 N2 n h5)). Qed.
Lemma lem1303765 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : term184 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1303764 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5) (@lem1303307 N1 N2 n h5)). Qed.
Lemma lem1303766 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : (term105 N1 N2 m) = (term184 x B1 B2 m n).
Proof. exact (prop_ext (fun h6 : term105 N1 N2 m => @lem1303765 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5) (fun h6 : term184 x B1 B2 m n => @lem1303308 N1 N2 m h4)). Qed.
Lemma lem1303767 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term105 N1 N2 m) (h5 : term105 N1 N2 n) : term184 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1303766 B1 x B2 m N1 N2 n h1 h2 h3 h4 h5) (@lem1303308 N1 N2 m h4)). Qed.
Lemma lem1303768 (B1 : nat) (x : nadd) (B2 : nat) (n : nat) (N1 : nat) (N2 : nat) (m : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term104 m N1 N2 n) (h5 : term105 N1 N2 m) : (term105 N1 N2 n) = (term184 x B1 B2 m n).
Proof. exact (prop_ext (fun h6 : term105 N1 N2 n => @lem1303767 B1 x B2 m N1 N2 n h1 h2 h3 h5 h6) (fun h6 : term184 x B1 B2 m n => @lem1303762 m N1 N2 n h4)). Qed.
Lemma lem1303769 (B1 : nat) (x : nadd) (B2 : nat) (n : nat) (N1 : nat) (N2 : nat) (m : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term104 m N1 N2 n) (h5 : term105 N1 N2 m) : term184 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1303768 B1 x B2 n N1 N2 m h1 h2 h3 h4 h5) (@lem1303762 m N1 N2 n h4)). Qed.
Lemma lem1303770 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term104 m N1 N2 n) : (term105 N1 N2 m) = (term184 x B1 B2 m n).
Proof. exact (prop_ext (fun h5 : term105 N1 N2 m => @lem1303769 B1 x B2 n N1 N2 m h1 h2 h3 h4 h5) (fun h5 : term184 x B1 B2 m n => @lem1303763 m N1 N2 n h4)). Qed.
Lemma lem1303771 (B1 : nat) (x : nadd) (B2 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) (h4 : term104 m N1 N2 n) : term184 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1303770 B1 x B2 m N1 N2 n h1 h2 h3 h4) (@lem1303763 m N1 N2 n h4)). Qed.
Lemma lem1303772 (m : nat) (n : nat) (B1 : nat) (N1 : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) : term185 N1 N2 x B1 B2 m n.
Proof. exact (fun h0 : term104 m N1 N2 n => @lem1303771 B1 x B2 m N1 N2 n h1 h2 h3 h0). Qed.
Lemma lem1303777 (m : nat) (B1 : nat) (N1 : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) : term186 N1 N2 x B1 B2 m.
Proof. exact (fun n : nat => @lem1303772 m n B1 N1 N2 x B2 h1 h2 h3). Qed.
Lemma lem1303782 (B1 : nat) (N1 : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) : term187 N1 N2 x B1 B2.
Proof. exact (fun m : nat => @lem1303777 m B1 N1 N2 x B2 h1 h2 h3). Qed.
Lemma lem1303783 (B1 : nat) (N1 : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) : term188 x B1 B2.
Proof. exact (ex_intro (term189 x B1 B2) (Nat.add N1 N2) (@lem1303782 B1 N1 N2 x B2 h1 h2 h3)). Qed.
Lemma lem1303784 (B1 : nat) (N1 : nat) (N2 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term103 N2 x B2) : term190 x.
Proof. exact (ex_intro (term191 x) (term192 B1 B2) (@lem1303783 B1 N1 N2 x B2 h1 h2 h3)). Qed.
Lemma lem1303785 (B1 : nat) (N1 : nat) (x : nadd) (B2 : nat) (h1 : term97 x B1) (h2 : term102 N1 x) (h3 : term94 x B2) : term190 x.
Proof. exact (ex_elim (@lem1303291 x B2 h3) (fun N2 : nat => fun h0 : term193 x B2 N2 => @lem1303784 B1 N1 N2 x B2 h1 h2 h0)). Qed.
Lemma lem1303786 (B1 : nat) (N1 : nat) (x : nadd) (h1 : term97 x B1) (h2 : term102 N1 x) : term190 x.
Proof. exact (ex_elim (@lem1303290 x) (fun B2 : nat => fun h0 : term194 x B2 => @lem1303785 B1 N1 x B2 h1 h2 h0)). Qed.
Lemma lem1303787 (N1 : nat) (x : nadd) (h1 : term102 N1 x) : term190 x.
Proof. exact (ex_elim (@lem1303294 x) (fun B1 : nat => fun h0 : term195 x B1 => @lem1303786 B1 N1 x h0 h1)). Qed.
Lemma lem1303788 (x : nadd) (h1 : term101 x) : term190 x.
Proof. exact (ex_elim (@lem1303303 x h1) (fun N1 : nat => fun h0 : term196 x N1 => @lem1303787 N1 x h0)). Qed.
Lemma lem1303789 (x : nadd) : term197 x.
Proof. exact (fun h0 : term101 x => @lem1303788 x h0). Qed.
Lemma lem1303790 (x : nadd) (h1 : term100 x) : term190 x.
Proof. exact (@lem1303789 x (@lem1303302 x h1)). Qed.
Lemma lem1303791 (x : nadd) : term198 x.
Proof. exact (fun h0 : term100 x => @lem1303790 x h0). Qed.
Lemma lem1303796 : term199.
Proof. exact (fun x : nadd => @lem1303791 x). Qed.
