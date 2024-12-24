Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1255398_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1254987 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254988 (p : nat) (d' : nat) (d''' : nat) (q : nat) (d'' : nat) : (term2 p d' d''' q d'') = (term3 p d' d''' q d'').
Proof. exact (@lem1254987 p (term4 d' d'' d''') (Nat.add q d'')). Qed.
Lemma lem1254996 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254997 (d' : nat) (d''' : nat) (q : nat) (d'' : nat) : (term5 d' d''' q d'') = (term6 d' d''' q d'').
Proof. exact (@lem1254996 (Nat.add d' d'') (S d''') (Nat.add q d'')). Qed.
Lemma lem1254999 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255000 (d' : nat) (d''' : nat) (q : nat) (d'' : nat) : (term6 d' d''' q d'') = (term7 d' d''' q d'').
Proof. exact (@lem1254999 d' d'' (term8 d''' q d'')). Qed.
Lemma lem1255007 (d' : nat) (d''' : nat) (q : nat) (d'' : nat) : (term5 d' d''' q d'') = (term7 d' d''' q d'').
Proof. exact (TRANS (@lem1254997 d' d''' q d'') (@lem1255000 d' d''' q d'')). Qed.
Lemma lem1255015 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255016 (q : nat) (d''' : nat) (d'' : nat) : (term8 d''' q d'') = (term9 q d''' d'').
Proof. exact (@lem1255015 q (S d''') d''). Qed.
Lemma lem1255024 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255025 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (@lem1255024 d'' (S d''')). Qed.
Lemma lem1255029 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1255030 (q : nat) (d'' : nat) (d''' : nat) : (term9 q d''' d'') = (term12 q d'' d''').
Proof. exact (MK_COMB (@lem1255029 q) (@lem1255025 d'' d''')). Qed.
Lemma lem1255032 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255033 (d'' : nat) (q : nat) (d''' : nat) : (term12 q d'' d''') = (term12 d'' q d''').
Proof. exact (@lem1255032 d'' q (S d''')). Qed.
Lemma lem1255043 (d'' : nat) (q : nat) (d''' : nat) : (term9 q d''' d'') = (term12 d'' q d''').
Proof. exact (TRANS (@lem1255030 q d'' d''') (@lem1255033 d'' q d''')). Qed.
Lemma lem1255044 (d'' : nat) (q : nat) (d''' : nat) : (term8 d''' q d'') = (term12 d'' q d''').
Proof. exact (TRANS (@lem1255016 q d''' d'') (@lem1255043 d'' q d''')). Qed.
Lemma lem1255045 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255046 (d'' : nat) (q : nat) (d''' : nat) : (term13 d''' q d'') = (term14 d'' q d''').
Proof. exact (MK_COMB (@lem1255045 d'') (@lem1255044 d'' q d''')). Qed.
Lemma lem1255053 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255054 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 d' d''' q d'') = (term15 d' d'' q d''').
Proof. exact (MK_COMB (@lem1255053 d') (@lem1255046 d'' q d''')). Qed.
Lemma lem1255061 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term5 d' d''' q d'') = (term15 d' d'' q d''').
Proof. exact (TRANS (@lem1255007 d' d''' q d'') (@lem1255054 d' d'' q d''')). Qed.
Lemma lem1255062 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255063 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term3 p d' d''' q d'') = (term16 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1255062 p) (@lem1255061 d' d'' q d''')). Qed.
Lemma lem1255065 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255066 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 p d' d'' q d''') = (term16 d' p d'' q d''').
Proof. exact (@lem1255065 d' p (term14 d'' q d''')). Qed.
Lemma lem1255074 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255075 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term17 p d'' q d''').
Proof. exact (@lem1255074 d'' p (term12 d'' q d''')). Qed.
Lemma lem1255083 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255084 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 p d'' q d''') = (term18 d'' p q d''').
Proof. exact (@lem1255083 d'' p (term11 q d''')). Qed.
Lemma lem1255100 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255101 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term17 p d'' q d''') = (term19 d'' p q d''').
Proof. exact (MK_COMB (@lem1255100 d'') (@lem1255084 d'' p q d''')). Qed.
Lemma lem1255108 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term19 d'' p q d''').
Proof. exact (TRANS (@lem1255075 p d'' q d''') (@lem1255101 d'' p q d''')). Qed.
Lemma lem1255109 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255110 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 d' p d'' q d''') = (term20 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1255109 d') (@lem1255108 d'' p q d''')). Qed.
Lemma lem1255117 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 p d' d'' q d''') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1255066 d' p d'' q d''') (@lem1255110 d' d'' p q d''')). Qed.
Lemma lem1255118 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term3 p d' d''' q d'') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1255063 p d' d'' q d''') (@lem1255117 d' d'' p q d''')). Qed.
Lemma lem1255119 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term2 p d' d''' q d'') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1254988 p d' d''' q d'') (@lem1255118 d' d'' p q d''')). Qed.
Lemma lem1255120 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255121 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term21 p d' d''' q d'') = (term22 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1255120) (@lem1255119 d' d'' p q d''')). Qed.
Lemma lem1255123 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255124 (p : nat) (q : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term23 q p d' d''' d'') = (term23 p q d' d''' d'').
Proof. exact (@lem1255123 p q (term24 d' d''' d'')). Qed.
Lemma lem1255132 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255133 (d' : nat) (q : nat) (d''' : nat) (d'' : nat) : (term25 q d' d''' d'') = (term25 d' q d''' d'').
Proof. exact (@lem1255132 d' q (term26 d''' d'')). Qed.
Lemma lem1255147 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255148 (d''' : nat) (d'' : nat) : (term26 d''' d'') = (term27 d''' d'').
Proof. exact (@lem1255147 d'' (S d''') d''). Qed.
Lemma lem1255156 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255157 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (@lem1255156 d'' (S d''')). Qed.
Lemma lem1255161 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255162 (d'' : nat) (d''' : nat) : (term27 d''' d'') = (term28 d'' d''').
Proof. exact (MK_COMB (@lem1255161 d'') (@lem1255157 d'' d''')). Qed.
Lemma lem1255169 (d'' : nat) (d''' : nat) : (term26 d''' d'') = (term28 d'' d''').
Proof. exact (TRANS (@lem1255148 d''' d'') (@lem1255162 d'' d''')). Qed.
Lemma lem1255170 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1255171 (q : nat) (d'' : nat) (d''' : nat) : (term24 q d''' d'') = (term29 q d'' d''').
Proof. exact (MK_COMB (@lem1255170 q) (@lem1255169 d'' d''')). Qed.
Lemma lem1255173 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255174 (q : nat) (d'' : nat) (d''' : nat) : (term29 q d'' d''') = (term30 q d'' d''').
Proof. exact (@lem1255173 d'' q (term11 d'' d''')). Qed.
Lemma lem1255182 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255183 (d'' : nat) (q : nat) (d''' : nat) : (term12 q d'' d''') = (term12 d'' q d''').
Proof. exact (@lem1255182 d'' q (S d''')). Qed.
Lemma lem1255193 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255194 (d'' : nat) (q : nat) (d''' : nat) : (term30 q d'' d''') = (term14 d'' q d''').
Proof. exact (MK_COMB (@lem1255193 d'') (@lem1255183 d'' q d''')). Qed.
Lemma lem1255201 (d'' : nat) (q : nat) (d''' : nat) : (term29 q d'' d''') = (term14 d'' q d''').
Proof. exact (TRANS (@lem1255174 q d'' d''') (@lem1255194 d'' q d''')). Qed.
Lemma lem1255202 (d'' : nat) (q : nat) (d''' : nat) : (term24 q d''' d'') = (term14 d'' q d''').
Proof. exact (TRANS (@lem1255171 q d'' d''') (@lem1255201 d'' q d''')). Qed.
Lemma lem1255203 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255204 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 d' q d''' d'') = (term15 d' d'' q d''').
Proof. exact (MK_COMB (@lem1255203 d') (@lem1255202 d'' q d''')). Qed.
Lemma lem1255211 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 q d' d''' d'') = (term15 d' d'' q d''').
Proof. exact (TRANS (@lem1255133 d' q d''' d'') (@lem1255204 d' d'' q d''')). Qed.
Lemma lem1255212 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255213 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term23 p q d' d''' d'') = (term16 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1255212 p) (@lem1255211 d' d'' q d''')). Qed.
Lemma lem1255215 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255216 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 p d' d'' q d''') = (term16 d' p d'' q d''').
Proof. exact (@lem1255215 d' p (term14 d'' q d''')). Qed.
Lemma lem1255224 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255225 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term17 p d'' q d''').
Proof. exact (@lem1255224 d'' p (term12 d'' q d''')). Qed.
Lemma lem1255233 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255234 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 p d'' q d''') = (term18 d'' p q d''').
Proof. exact (@lem1255233 d'' p (term11 q d''')). Qed.
Lemma lem1255250 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255251 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term17 p d'' q d''') = (term19 d'' p q d''').
Proof. exact (MK_COMB (@lem1255250 d'') (@lem1255234 d'' p q d''')). Qed.
Lemma lem1255258 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term19 d'' p q d''').
Proof. exact (TRANS (@lem1255225 p d'' q d''') (@lem1255251 d'' p q d''')). Qed.
Lemma lem1255259 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255260 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 d' p d'' q d''') = (term20 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1255259 d') (@lem1255258 d'' p q d''')). Qed.
Lemma lem1255267 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 p d' d'' q d''') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1255216 d' p d'' q d''') (@lem1255260 d' d'' p q d''')). Qed.
Lemma lem1255268 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term23 p q d' d''' d'') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1255213 p d' d'' q d''') (@lem1255267 d' d'' p q d''')). Qed.
Lemma lem1255269 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term23 q p d' d''' d'') = (term20 d' d'' p q d''').
Proof. exact (TRANS (@lem1255124 p q d' d''' d'') (@lem1255268 d' d'' p q d''')). Qed.
Lemma lem1255270 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term2 p d' d''' q d'') = (term23 q p d' d''' d'')) = ((term20 d' d'' p q d''') = (term20 d' d'' p q d''')).
Proof. exact (MK_COMB (@lem1255121 d' d'' p q d''') (@lem1255269 d' d'' p q d''')). Qed.
Lemma lem1255272 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1255273 (x : nat) : (x = x) = True.
Proof. exact (@lem1255272 nat x). Qed.
Lemma lem1255274 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term20 d' d'' p q d''') = (term20 d' d'' p q d''')) = True.
Proof. exact (@lem1255273 (term20 d' d'' p q d''')). Qed.
Lemma lem1255275 (q : nat) (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 p d' d''' q d'') = (term23 q p d' d''' d'')) = True.
Proof. exact (TRANS (@lem1255270 d' d'' p q d''') (@lem1255274 d' d'' p q d''')). Qed.
Lemma lem1255276 (q : nat) (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : True = ((term2 p d' d''' q d'') = (term23 q p d' d''' d'')).
Proof. exact (SYM (@lem1255275 q p d' d''' d'')). Qed.
Lemma lem1255277 (q : nat) (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 p d' d''' q d'') = (term23 q p d' d''' d'').
Proof. exact (EQ_MP (@lem1255276 q p d' d''' d'') (@lem0)). Qed.
Lemma lem1255281 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255282 (p : nat) (q : nat) (d' : nat) : (term0 p q d') = (term1 p q d').
Proof. exact (@lem1255281 p q d'). Qed.
Lemma lem1255290 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255291 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1255290 d' q). Qed.
Lemma lem1255295 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255296 (p : nat) (d' : nat) (q : nat) : (term1 p q d') = (term1 p d' q).
Proof. exact (MK_COMB (@lem1255295 p) (@lem1255291 d' q)). Qed.
Lemma lem1255298 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255299 (d' : nat) (p : nat) (q : nat) : (term1 p d' q) = (term1 d' p q).
Proof. exact (@lem1255298 d' p q). Qed.
Lemma lem1255309 (d' : nat) (p : nat) (q : nat) : (term1 p q d') = (term1 d' p q).
Proof. exact (TRANS (@lem1255296 p d' q) (@lem1255299 d' p q)). Qed.
Lemma lem1255310 (d' : nat) (p : nat) (q : nat) : (term0 p q d') = (term1 d' p q).
Proof. exact (TRANS (@lem1255282 p q d') (@lem1255309 d' p q)). Qed.
Lemma lem1255311 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255312 (d' : nat) (p : nat) (q : nat) : (term31 p q d') = (term32 d' p q).
Proof. exact (MK_COMB (@lem1255311) (@lem1255310 d' p q)). Qed.
Lemma lem1255314 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255315 (p : nat) (q : nat) (d' : nat) : (term1 q p d') = (term1 p q d').
Proof. exact (@lem1255314 p q d'). Qed.
Lemma lem1255323 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255324 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1255323 d' q). Qed.
Lemma lem1255328 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1255329 (p : nat) (d' : nat) (q : nat) : (term1 p q d') = (term1 p d' q).
Proof. exact (MK_COMB (@lem1255328 p) (@lem1255324 d' q)). Qed.
Lemma lem1255331 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255332 (d' : nat) (p : nat) (q : nat) : (term1 p d' q) = (term1 d' p q).
Proof. exact (@lem1255331 d' p q). Qed.
Lemma lem1255342 (d' : nat) (p : nat) (q : nat) : (term1 p q d') = (term1 d' p q).
Proof. exact (TRANS (@lem1255329 p d' q) (@lem1255332 d' p q)). Qed.
Lemma lem1255343 (d' : nat) (p : nat) (q : nat) : (term1 q p d') = (term1 d' p q).
Proof. exact (TRANS (@lem1255315 p q d') (@lem1255342 d' p q)). Qed.
Lemma lem1255344 (d' : nat) (p : nat) (q : nat) : ((term0 p q d') = (term1 q p d')) = ((term1 d' p q) = (term1 d' p q)).
Proof. exact (MK_COMB (@lem1255312 d' p q) (@lem1255343 d' p q)). Qed.
Lemma lem1255346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1255347 (x : nat) : (x = x) = True.
Proof. exact (@lem1255346 nat x). Qed.
Lemma lem1255348 (d' : nat) (p : nat) (q : nat) : ((term1 d' p q) = (term1 d' p q)) = True.
Proof. exact (@lem1255347 (term1 d' p q)). Qed.
Lemma lem1255349 (q : nat) (p : nat) (d' : nat) : ((term0 p q d') = (term1 q p d')) = True.
Proof. exact (TRANS (@lem1255344 d' p q) (@lem1255348 d' p q)). Qed.
Lemma lem1255350 (q : nat) (p : nat) (d' : nat) : True = ((term0 p q d') = (term1 q p d')).
Proof. exact (SYM (@lem1255349 q p d')). Qed.
Lemma lem1255351 (q : nat) (p : nat) (d' : nat) : (term0 p q d') = (term1 q p d').
Proof. exact (EQ_MP (@lem1255350 q p d') (@lem0)). Qed.
Lemma lem1255352 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1255353 (q : nat) (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term21 p d' d''' q d'') = (term33 q p d' d''' d'').
Proof. exact (MK_COMB (@lem1255352) (@lem1255277 q p d' d''' d'')). Qed.
Lemma lem1255354 (d''' : nat) (d'' : nat) (q : nat) (p : nat) (d' : nat) : ((term2 p d' d''' q d'') = (term0 p q d')) = ((term23 q p d' d''' d'') = (term1 q p d')).
Proof. exact (MK_COMB (@lem1255353 q p d' d''' d'') (@lem1255351 q p d')). Qed.
Lemma lem1255361 (m : nat) : term34 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1255362 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1255363 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem1255362 m) (@lem1255361 m)). Qed.
Lemma lem1255364 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem1255363 m n). Qed.
Lemma lem1255365 (m : nat) (n : nat) : (term36 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1255367 (m : nat) : term37 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1255368 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1255369 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1255368 m) (@lem1255367 m)). Qed.
Lemma lem1255370 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1255369 m n). Qed.
Lemma lem1255371 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1255372 (m : nat) (n : nat) : term40 m n.
Proof. exact (EQ_MP (@lem1255371 m n) (@lem1255370 m n)). Qed.
Lemma lem1255373 (m : nat) (n : nat) (p : nat) : term41 m n p.
Proof. exact (@lem1255372 m n p). Qed.
Lemma lem1255374 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term41 m n p)). Qed.
Lemma lem1255377 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1255374 m n p) (@lem1255373 m n p)). Qed.
Lemma lem1255378 (q : nat) (d''' : nat) (d'' : nat) (p : nat) (d' : nat) : ((term23 q p d' d''' d'') = (term1 q p d')) = ((term25 p d' d''' d'') = (Nat.add p d')).
Proof. exact (@lem1255377 q (term25 p d' d''' d'') (Nat.add p d')). Qed.
Lemma lem1255380 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1255374 m n p) (@lem1255373 m n p)). Qed.
Lemma lem1255381 (p : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term25 p d' d''' d'') = (Nat.add p d')) = ((term24 d' d''' d'') = d').
Proof. exact (@lem1255380 p (term24 d' d''' d'') d'). Qed.
Lemma lem1255383 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1255365 m n) (@lem1255364 m n)). Qed.
Lemma lem1255388 (d' : nat) (d''' : nat) (d'' : nat) : ((term24 d' d''' d'') = d') = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (@lem1255383 d' (term26 d''' d'')). Qed.
Lemma lem1255389 (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term25 p d' d''' d'') = (Nat.add p d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1255381 p d''' d'' d') (@lem1255388 d' d''' d'')). Qed.
Lemma lem1255390 (q : nat) (p : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term23 q p d' d''' d'') = (term1 q p d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1255378 q d''' d'' p d') (@lem1255389 p d' d''' d'')). Qed.
Lemma lem1255391 (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term42 d''' d'' p q d') = (term42 d''' d'' p q d').
Proof. exact (eq_refl (term42 d''' d'' p q d')). Qed.
Lemma lem1255392 (p : nat) (q : nat) (d' : nat) (d''' : nat) (d'' : nat) : (((term2 p d' d''' q d'') = (term0 p q d')) = ((term23 q p d' d''' d'') = (term1 q p d'))) = (((term2 p d' d''' q d'') = (term0 p q d')) = ((term26 d''' d'') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1255391 d''' d'' p q d') (@lem1255390 q p d' d''' d'')). Qed.
Lemma lem1255393 (p : nat) (q : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 p d' d''' q d'') = (term0 p q d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1255392 p q d' d''' d'') (@lem1255354 d''' d'' q p d')). Qed.
Lemma lem1255394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1255395 (p : nat) (q : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term43 d''' d'' p q d') = (term44 d''' d'').
Proof. exact (MK_COMB (@lem1255394) (@lem1255393 p q d' d''' d'')). Qed.
Lemma lem1255396 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1255397 (p : nat) (q : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term45 d''' d'' p q d') = (term46 d''' d'').
Proof. exact (MK_COMB (@lem1255395 p q d' d''' d'') (@lem1255396)). Qed.
Lemma lem1255398 (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term46 d''' d'') = (term45 d''' d'' p q d').
Proof. exact (SYM (@lem1255397 p q d' d''' d'')). Qed.
