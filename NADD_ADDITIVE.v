Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADDITIVE_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_EQ_0_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DIST_LADD_0_spec.
Require Import DIST_LMUL_spec.
Require Import DIST_SYM_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD2_spec.
Require Import LE_ADDR_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_CAUCHY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1259721_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Require Import thm272809_spec.
Require Import thm513079_spec.
Require Import thm513870_spec.
Require Import thm514290_spec.
Require Import thm7_spec.
Lemma lem1264304 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1264305 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1264304 h1 m). Qed.
Lemma lem1264306 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1264307 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1264306 m) (@lem1264305 m h1)). Qed.
Lemma lem1264308 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1264307 m h1 n). Qed.
Lemma lem1264309 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1264310 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1264309 m n) (@lem1264308 m n h1)). Qed.
Lemma lem1264311 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem1264310 m n h1 p). Qed.
Lemma lem1264312 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1264313 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem1264312 m n p) (@lem1264311 m n p h1)). Qed.
Lemma lem1264314 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem1264313 m n p h1 q). Qed.
Lemma lem1264315 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1264316 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem1264315 m n p q) (@lem1264314 m n p q h1)). Qed.
Lemma lem1264317 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem1264318 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1264316 m n p q h1 (@lem1264317 m p n q h2)). Qed.
Lemma lem1264319 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem1264318 m p n q h0 h1). Qed.
Lemma lem1264320 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1264321 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1264319 m p n q h2 (@lem1264320 h1)). Qed.
Lemma lem1264322 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem1264321 m p n q h1 h0). Qed.
Lemma lem1264323 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem1264322 m n p q h1). Qed.
Lemma lem1264324 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem1264323 m n p h1). Qed.
Lemma lem1264325 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1264324 m n h1). Qed.
Lemma lem1264326 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1264325 m h1). Qed.
Lemma lem1264327 : term12.
Proof. exact (fun h0 : term0 => @lem1264326 h0). Qed.
Lemma lem1264328 : term0.
Proof. exact (@lem1264327 (@lem101399)). Qed.
Lemma lem1264329 (m : nat) : term1 m.
Proof. exact (@lem1264328 m). Qed.
Lemma lem1264330 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1264331 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1264330 m) (@lem1264329 m)). Qed.
Lemma lem1264332 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1264331 m n). Qed.
Lemma lem1264333 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1264334 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1264333 m n) (@lem1264332 m n)). Qed.
Lemma lem1264335 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1264334 m n p). Qed.
Lemma lem1264336 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1264337 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem1264336 m n p) (@lem1264335 m n p)). Qed.
Lemma lem1264338 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem1264337 m n p q). Qed.
Lemma lem1264339 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1264345 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1264346 : term14.
Proof. exact (proj2 (@lem1264345)). Qed.
Lemma lem1264367 : term15.
Proof. exact (proj1 (@lem1264346)). Qed.
Lemma lem1264368 (n : nat) : term16 n.
Proof. exact (@lem1264367 n). Qed.
Lemma lem1264369 (n : nat) : (term16 n) = ((term17 n) = n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem1264379 (m : nat) : term18 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1264380 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1264381 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1264380 m) (@lem1264379 m)). Qed.
Lemma lem1264382 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1264381 m n). Qed.
Lemma lem1264383 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1264384 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem1264383 n m) (@lem1264382 m n)). Qed.
Lemma lem1264385 (n : nat) (m : nat) (p : nat) : term22 n m p.
Proof. exact (@lem1264384 n m p). Qed.
Lemma lem1264386 (n : nat) (m : nat) (p : nat) : (term22 n m p) = ((term23 m n p) = (term24 n m p)).
Proof. exact (eq_refl (term22 n m p)). Qed.
Lemma lem1264388 (m : nat) : term25 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1264389 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1264390 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1264389 m) (@lem1264388 m)). Qed.
Lemma lem1264391 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem1264390 m n). Qed.
Lemma lem1264392 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1264393 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem1264392 m n) (@lem1264391 m n)). Qed.
Lemma lem1264394 (m : nat) (n : nat) (p : nat) : term29 m n p.
Proof. exact (@lem1264393 m n p). Qed.
Lemma lem1264395 (m : nat) (n : nat) (p : nat) : (term29 m n p) = ((term30 m n p) = (term31 m n p)).
Proof. exact (eq_refl (term29 m n p)). Qed.
Lemma lem1264945 : term32.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
Lemma lem1264946 : term33.
Proof. exact (proj2 (@lem1264945)). Qed.
Lemma lem1264947 : term34.
Proof. exact (proj2 (@lem1264946)). Qed.
Lemma lem1264948 : term35.
Proof. exact (proj2 (@lem1264947)). Qed.
Lemma lem1264949 : term36.
Proof. exact (proj2 (@lem1264948)). Qed.
Lemma lem1264950 : term37.
Proof. exact (proj2 (@lem1264949)). Qed.
Lemma lem1264951 : term38.
Proof. exact (proj2 (@lem1264950)). Qed.
Lemma lem1264952 : term39.
Proof. exact (proj2 (@lem1264951)). Qed.
Lemma lem1264953 : term40.
Proof. exact (proj2 (@lem1264952)). Qed.
Lemma lem1264954 : term41.
Proof. exact (proj2 (@lem1264953)). Qed.
Lemma lem1264955 (m : nat) : term42 m.
Proof. exact (@lem1264954 m). Qed.
Lemma lem1264956 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem1264957 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1264956 m) (@lem1264955 m)). Qed.
Lemma lem1264958 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem1264957 m n). Qed.
Lemma lem1264959 (m : nat) (n : nat) : (term44 m n) = ((term45 m n) = (term46 m n)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem1264961 : term47.
Proof. exact (proj1 (@lem1264953)). Qed.
Lemma lem1264962 (m : nat) : term48 m.
Proof. exact (@lem1264961 m). Qed.
Lemma lem1264963 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem1264964 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem1264963 m) (@lem1264962 m)). Qed.
Lemma lem1264965 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem1264964 m n). Qed.
Lemma lem1264966 (m : nat) (n : nat) : (term50 m n) = ((term51 m n) = (term52 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem1264990 : term53.
Proof. exact (proj1 (@lem1264948)). Qed.
Lemma lem1264991 (n : nat) : term54 n.
Proof. exact (@lem1264990 n). Qed.
Lemma lem1264992 (n : nat) : (term54 n) = ((term55 n) = (BIT1 n)).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem1264999 : term56.
Proof. exact (proj1 (@lem1264945)). Qed.
Lemma lem1265000 (m : nat) : term57 m.
Proof. exact (@lem1264999 m). Qed.
Lemma lem1265001 (m : nat) : (term57 m) = (term58 m).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem1265002 (m : nat) : term58 m.
Proof. exact (EQ_MP (@lem1265001 m) (@lem1265000 m)). Qed.
Lemma lem1265003 (m : nat) (n : nat) : term59 m n.
Proof. exact (@lem1265002 m n). Qed.
Lemma lem1265004 (m : nat) (n : nat) : (term59 m n) = ((term60 m n) = (term61 m n)).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem1265022 : term62.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem1265023 : term63.
Proof. exact (proj2 (@lem1265022)). Qed.
Lemma lem1265042 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem1265004 m n) (@lem1265003 m n)). Qed.
Lemma lem1265043 : term64 = term65.
Proof. exact (@lem1265042 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1265045 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem1264959 m n) (@lem1264958 m n)). Qed.
Lemma lem1265046 : term66 = term67.
Proof. exact (@lem1265045 0 0). Qed.
Lemma lem1265048 : (Nat.add 0 0) = 0.
Proof. exact (proj1 (@lem1264946)). Qed.
Lemma lem1265049 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1265050 : term68 = (S 0).
Proof. exact (MK_COMB (@lem1265049) (@lem1265048)). Qed.
Lemma lem1265052 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem1265023)). Qed.
Lemma lem1265053 : term68 = (BIT1 0).
Proof. exact (TRANS (@lem1265050) (@lem1265052)). Qed.
Lemma lem1265054 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem1265055 : term67 = term69.
Proof. exact (MK_COMB (@lem1265054) (@lem1265053)). Qed.
Lemma lem1265056 : term66 = term69.
Proof. exact (TRANS (@lem1265046) (@lem1265055)). Qed.
Lemma lem1265057 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1265058 : term65 = term70.
Proof. exact (MK_COMB (@lem1265057) (@lem1265056)). Qed.
Lemma lem1265059 : term64 = term70.
Proof. exact (TRANS (@lem1265043) (@lem1265058)). Qed.
Lemma lem1265060 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem1265061 : term72 = term73.
Proof. exact (MK_COMB (@lem1265060) (@lem1265059)). Qed.
Lemma lem1265063 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem1265004 m n) (@lem1265003 m n)). Qed.
Lemma lem1265064 : term73 = term74.
Proof. exact (@lem1265063 (BIT1 0) term69). Qed.
Lemma lem1265066 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (EQ_MP (@lem1264966 m n) (@lem1264965 m n)). Qed.
Lemma lem1265067 : term75 = term76.
Proof. exact (@lem1265066 0 (BIT1 0)). Qed.
Lemma lem1265069 (n : nat) : (term55 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem1264992 n) (@lem1264991 n)). Qed.
Lemma lem1265070 : term77 = (BIT1 0).
Proof. exact (@lem1265069 0). Qed.
Lemma lem1265071 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem1265072 : term76 = term78.
Proof. exact (MK_COMB (@lem1265071) (@lem1265070)). Qed.
Lemma lem1265073 : term75 = term78.
Proof. exact (TRANS (@lem1265067) (@lem1265072)). Qed.
Lemma lem1265074 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1265075 : term74 = term79.
Proof. exact (MK_COMB (@lem1265074) (@lem1265073)). Qed.
Lemma lem1265076 : term73 = term79.
Proof. exact (TRANS (@lem1265064) (@lem1265075)). Qed.
Lemma lem1265077 : term72 = term79.
Proof. exact (TRANS (@lem1265061) (@lem1265076)). Qed.
Lemma lem1265079 (m : nat) : term80 m.
Proof. exact (@lem1259721 m). Qed.
Lemma lem1265080 (m : nat) : (term80 m) = (term81 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem1265081 (m : nat) : term81 m.
Proof. exact (EQ_MP (@lem1265080 m) (@lem1265079 m)). Qed.
Lemma lem1265082 (m : nat) (n : nat) : term82 m n.
Proof. exact (@lem1265081 m n). Qed.
Lemma lem1265083 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem1265084 (m : nat) (n : nat) : term83 m n.
Proof. exact (EQ_MP (@lem1265083 m n) (@lem1265082 m n)). Qed.
Lemma lem1265085 (m : nat) (n : nat) (p : nat) : term84 m n p.
Proof. exact (@lem1265084 m n p). Qed.
Lemma lem1265086 (m : nat) (p : nat) (n : nat) : (term84 m n p) = (term85 m p n).
Proof. exact (eq_refl (term84 m n p)). Qed.
Lemma lem1265087 (m : nat) (p : nat) (n : nat) : term85 m p n.
Proof. exact (EQ_MP (@lem1265086 m p n) (@lem1265085 m n p)). Qed.
Lemma lem1265088 (m : nat) (p : nat) (n : nat) (q : nat) : term86 m p n q.
Proof. exact (@lem1265087 m p n q). Qed.
Lemma lem1265089 (m : nat) (p : nat) (n : nat) (q : nat) : (term86 m p n q) = (term87 m p n q).
Proof. exact (eq_refl (term86 m p n q)). Qed.
Lemma lem1265090 (m : nat) (p : nat) (n : nat) (q : nat) : term87 m p n q.
Proof. exact (EQ_MP (@lem1265089 m p n q) (@lem1265088 m p n q)). Qed.
Lemma lem1265091 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem1265092 (m : nat) (h1 : term88) : term89 m.
Proof. exact (@lem1265091 h1 m). Qed.
Lemma lem1265093 (m : nat) : (term89 m) = (term90 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1265094 (m : nat) (h1 : term88) : term90 m.
Proof. exact (EQ_MP (@lem1265093 m) (@lem1265092 m h1)). Qed.
Lemma lem1265095 (m : nat) (n : nat) (h1 : term88) : term91 m n.
Proof. exact (@lem1265094 m h1 n). Qed.
Lemma lem1265096 (n : nat) (m : nat) : (term91 m n) = (term92 n m).
Proof. exact (eq_refl (term91 m n)). Qed.
Lemma lem1265097 (n : nat) (m : nat) (h1 : term88) : term92 n m.
Proof. exact (EQ_MP (@lem1265096 n m) (@lem1265095 m n h1)). Qed.
Lemma lem1265098 (n : nat) (m : nat) (p : nat) (h1 : term88) : term93 n m p.
Proof. exact (@lem1265097 n m h1 p). Qed.
Lemma lem1265099 (n : nat) (m : nat) (p : nat) : (term93 n m p) = (term94 n m p).
Proof. exact (eq_refl (term93 n m p)). Qed.
Lemma lem1265100 (n : nat) (m : nat) (p : nat) (h1 : term88) : term94 n m p.
Proof. exact (EQ_MP (@lem1265099 n m p) (@lem1265098 n m p h1)). Qed.
Lemma lem1265101 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1265102 (p : nat) (m : nat) (n : nat) (h1 : term88) (h2 : Peano.le m n) : term95 n m p.
Proof. exact (@lem1265100 n m p h1 (@lem1265101 m n h2)). Qed.
Lemma lem1265103 (m : nat) (n : nat) (h1 : term88) (h2 : Peano.le m n) : term96 n m.
Proof. exact (fun p : nat => @lem1265102 p m n h1 h2). Qed.
Lemma lem1265104 (n : nat) (m : nat) (h1 : term88) : term97 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1265103 m n h1 h0). Qed.
Lemma lem1265105 (m : nat) (h1 : term88) : term98 m.
Proof. exact (fun n : nat => @lem1265104 n m h1). Qed.
Lemma lem1265106 (h1 : term88) : term99.
Proof. exact (fun m : nat => @lem1265105 m h1). Qed.
Lemma lem1265107 : term100.
Proof. exact (fun h0 : term88 => @lem1265106 h0). Qed.
Lemma lem1265108 : term99.
Proof. exact (@lem1265107 (@lem272809)). Qed.
Lemma lem1265109 (m : nat) : term101 m.
Proof. exact (@lem1265108 m). Qed.
Lemma lem1265110 (m : nat) : (term101 m) = (term98 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem1265111 (m : nat) : term98 m.
Proof. exact (EQ_MP (@lem1265110 m) (@lem1265109 m)). Qed.
Lemma lem1265112 (m : nat) (n : nat) : term102 m n.
Proof. exact (@lem1265111 m n). Qed.
Lemma lem1265113 (n : nat) (m : nat) : (term102 m n) = (term97 n m).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem1265116 (n : nat) (m : nat) : term97 n m.
Proof. exact (EQ_MP (@lem1265113 n m) (@lem1265112 m n)). Qed.
Lemma lem1265117 (m : nat) (n : nat) (p : nat) (q : nat) : term103 m n p q.
Proof. exact (@lem1265116 (term104 m p n q) (term105 m n p q)). Qed.
Lemma lem1265118 (m : nat) (n : nat) (p : nat) (q : nat) : term106 m n p q.
Proof. exact (@lem1265117 m n p q (@lem1265090 m p n q)). Qed.
Lemma lem1265119 (m : nat) (n : nat) (p : nat) : term107 m n p.
Proof. exact (fun q : nat => @lem1265118 m n p q). Qed.
Lemma lem1265120 (m : nat) (n : nat) : term108 m n.
Proof. exact (fun p : nat => @lem1265119 m n p). Qed.
Lemma lem1265121 (m : nat) : term109 m.
Proof. exact (fun n : nat => @lem1265120 m n). Qed.
Lemma lem1265122 : term110.
Proof. exact (fun m : nat => @lem1265121 m). Qed.
Lemma lem1265123 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1265124 (m : nat) (h1 : term110) : term111 m.
Proof. exact (@lem1265123 h1 m). Qed.
Lemma lem1265125 (m : nat) : (term111 m) = (term109 m).
Proof. exact (eq_refl (term111 m)). Qed.
Lemma lem1265126 (m : nat) (h1 : term110) : term109 m.
Proof. exact (EQ_MP (@lem1265125 m) (@lem1265124 m h1)). Qed.
Lemma lem1265127 (m : nat) (n : nat) (h1 : term110) : term112 m n.
Proof. exact (@lem1265126 m h1 n). Qed.
Lemma lem1265128 (m : nat) (n : nat) : (term112 m n) = (term108 m n).
Proof. exact (eq_refl (term112 m n)). Qed.
Lemma lem1265129 (m : nat) (n : nat) (h1 : term110) : term108 m n.
Proof. exact (EQ_MP (@lem1265128 m n) (@lem1265127 m n h1)). Qed.
Lemma lem1265130 (m : nat) (n : nat) (p : nat) (h1 : term110) : term113 m n p.
Proof. exact (@lem1265129 m n h1 p). Qed.
Lemma lem1265131 (m : nat) (n : nat) (p : nat) : (term113 m n p) = (term107 m n p).
Proof. exact (eq_refl (term113 m n p)). Qed.
Lemma lem1265132 (m : nat) (n : nat) (p : nat) (h1 : term110) : term107 m n p.
Proof. exact (EQ_MP (@lem1265131 m n p) (@lem1265130 m n p h1)). Qed.
Lemma lem1265133 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term110) : term114 m n p q.
Proof. exact (@lem1265132 m n p h1 q). Qed.
Lemma lem1265134 (m : nat) (n : nat) (p : nat) (q : nat) : (term114 m n p q) = (term106 m n p q).
Proof. exact (eq_refl (term114 m n p q)). Qed.
Lemma lem1265135 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term110) : term106 m n p q.
Proof. exact (EQ_MP (@lem1265134 m n p q) (@lem1265133 m n p q h1)). Qed.
Lemma lem1265136 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term110) : term115 m n p q p'.
Proof. exact (@lem1265135 m n p q h1 p'). Qed.
Lemma lem1265137 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term115 m n p q p') = (term116 m n p q p').
Proof. exact (eq_refl (term115 m n p q p')). Qed.
Lemma lem1265138 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term110) : term116 m n p q p'.
Proof. exact (EQ_MP (@lem1265137 m n p q p') (@lem1265136 m n p q p' h1)). Qed.
Lemma lem1265139 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term117 m p n q p') : term117 m p n q p'.
Proof. exact (h1). Qed.
Lemma lem1265140 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term110) (h2 : term117 m p n q p') : term118 m n p q p'.
Proof. exact (@lem1265138 m n p q p' h1 (@lem1265139 m p n q p' h2)). Qed.
Lemma lem1265141 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term117 m p n q p') : term119 m n p q p'.
Proof. exact (fun h0 : term110 => @lem1265140 m p n q p' h0 h1). Qed.
Lemma lem1265142 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1265143 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term110) (h2 : term117 m p n q p') : term118 m n p q p'.
Proof. exact (@lem1265141 m p n q p' h2 (@lem1265142 h1)). Qed.
Lemma lem1265144 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term110) : term116 m n p q p'.
Proof. exact (fun h0 : term117 m p n q p' => @lem1265143 m p n q p' h1 h0). Qed.
Lemma lem1265145 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term110) : term106 m n p q.
Proof. exact (fun p' : nat => @lem1265144 m n p q p' h1). Qed.
Lemma lem1265146 (m : nat) (n : nat) (p : nat) (h1 : term110) : term107 m n p.
Proof. exact (fun q : nat => @lem1265145 m n p q h1). Qed.
Lemma lem1265147 (m : nat) (n : nat) (h1 : term110) : term108 m n.
Proof. exact (fun p : nat => @lem1265146 m n p h1). Qed.
Lemma lem1265148 (m : nat) (h1 : term110) : term109 m.
Proof. exact (fun n : nat => @lem1265147 m n h1). Qed.
Lemma lem1265149 (h1 : term110) : term110.
Proof. exact (fun m : nat => @lem1265148 m h1). Qed.
Lemma lem1265150 : term120.
Proof. exact (fun h0 : term110 => @lem1265149 h0). Qed.
Lemma lem1265151 : term110.
Proof. exact (@lem1265150 (@lem1265122)). Qed.
Lemma lem1265152 (m : nat) : term111 m.
Proof. exact (@lem1265151 m). Qed.
Lemma lem1265153 (m : nat) : (term111 m) = (term109 m).
Proof. exact (eq_refl (term111 m)). Qed.
Lemma lem1265154 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem1265153 m) (@lem1265152 m)). Qed.
Lemma lem1265155 (m : nat) (n : nat) : term112 m n.
Proof. exact (@lem1265154 m n). Qed.
Lemma lem1265156 (m : nat) (n : nat) : (term112 m n) = (term108 m n).
Proof. exact (eq_refl (term112 m n)). Qed.
Lemma lem1265157 (m : nat) (n : nat) : term108 m n.
Proof. exact (EQ_MP (@lem1265156 m n) (@lem1265155 m n)). Qed.
Lemma lem1265158 (m : nat) (n : nat) (p : nat) : term113 m n p.
Proof. exact (@lem1265157 m n p). Qed.
Lemma lem1265159 (m : nat) (n : nat) (p : nat) : (term113 m n p) = (term107 m n p).
Proof. exact (eq_refl (term113 m n p)). Qed.
Lemma lem1265160 (m : nat) (n : nat) (p : nat) : term107 m n p.
Proof. exact (EQ_MP (@lem1265159 m n p) (@lem1265158 m n p)). Qed.
Lemma lem1265161 (m : nat) (n : nat) (p : nat) (q : nat) : term114 m n p q.
Proof. exact (@lem1265160 m n p q). Qed.
Lemma lem1265162 (m : nat) (n : nat) (p : nat) (q : nat) : (term114 m n p q) = (term106 m n p q).
Proof. exact (eq_refl (term114 m n p q)). Qed.
Lemma lem1265163 (m : nat) (n : nat) (p : nat) (q : nat) : term106 m n p q.
Proof. exact (EQ_MP (@lem1265162 m n p q) (@lem1265161 m n p q)). Qed.
Lemma lem1265164 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term115 m n p q p'.
Proof. exact (@lem1265163 m n p q p'). Qed.
Lemma lem1265165 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term115 m n p q p') = (term116 m n p q p').
Proof. exact (eq_refl (term115 m n p q p')). Qed.
Lemma lem1265167 (m : nat) : term25 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1265168 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1265169 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1265168 m) (@lem1265167 m)). Qed.
Lemma lem1265170 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem1265169 m n). Qed.
Lemma lem1265171 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1265172 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem1265171 m n) (@lem1265170 m n)). Qed.
Lemma lem1265173 (m : nat) (n : nat) (p : nat) : term29 m n p.
Proof. exact (@lem1265172 m n p). Qed.
Lemma lem1265174 (m : nat) (n : nat) (p : nat) : (term29 m n p) = ((term30 m n p) = (term31 m n p)).
Proof. exact (eq_refl (term29 m n p)). Qed.
Lemma lem1265176 (m : nat) : term18 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1265177 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1265178 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1265177 m) (@lem1265176 m)). Qed.
Lemma lem1265179 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1265178 m n). Qed.
Lemma lem1265180 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1265181 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem1265180 n m) (@lem1265179 m n)). Qed.
Lemma lem1265182 (n : nat) (m : nat) (p : nat) : term22 n m p.
Proof. exact (@lem1265181 n m p). Qed.
Lemma lem1265183 (n : nat) (m : nat) (p : nat) : (term22 n m p) = ((term23 m n p) = (term24 n m p)).
Proof. exact (eq_refl (term22 n m p)). Qed.
Lemma lem1265185 (m : nat) : term121 m.
Proof. exact (@lem1245388 m). Qed.
Lemma lem1265186 (m : nat) : (term121 m) = (term122 m).
Proof. exact (eq_refl (term121 m)). Qed.
Lemma lem1265187 (m : nat) : term122 m.
Proof. exact (EQ_MP (@lem1265186 m) (@lem1265185 m)). Qed.
Lemma lem1265188 (m : nat) (n : nat) : term123 m n.
Proof. exact (@lem1265187 m n). Qed.
Lemma lem1265189 (n : nat) (m : nat) : (term123 m n) = (term124 n m).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem1265190 (n : nat) (m : nat) : term124 n m.
Proof. exact (EQ_MP (@lem1265189 n m) (@lem1265188 m n)). Qed.
Lemma lem1265191 (n : nat) (m : nat) (p : nat) : term125 n m p.
Proof. exact (@lem1265190 n m p). Qed.
Lemma lem1265192 (n : nat) (m : nat) (p : nat) : (term125 n m p) = ((term126 m n p) = (term127 n m p)).
Proof. exact (eq_refl (term125 n m p)). Qed.
Lemma lem1265197 (m : nat) (n : nat) (p : nat) (h1 : (term128 n m p) = (term129 m n p)) : (term128 n m p) = (term129 m n p).
Proof. exact (h1). Qed.
Lemma lem1265198 (m : nat) (n : nat) (p : nat) (h1 : (term128 n m p) = (term129 m n p)) : (term129 m n p) = (term128 n m p).
Proof. exact (SYM (@lem1265197 m n p h1)). Qed.
Lemma lem1265199 (n : nat) (m : nat) (p : nat) (h1 : (term129 m n p) = (term128 n m p)) : (term129 m n p) = (term128 n m p).
Proof. exact (h1). Qed.
Lemma lem1265200 (n : nat) (m : nat) (p : nat) (h1 : (term129 m n p) = (term128 n m p)) : (term128 n m p) = (term129 m n p).
Proof. exact (SYM (@lem1265199 n m p h1)). Qed.
Lemma lem1265201 (n : nat) (m : nat) (p : nat) : ((term128 n m p) = (term129 m n p)) = ((term129 m n p) = (term128 n m p)).
Proof. exact (prop_ext (fun h1 : (term128 n m p) = (term129 m n p) => @lem1265198 m n p h1) (fun h1 : (term129 m n p) = (term128 n m p) => @lem1265200 n m p h1)). Qed.
Lemma lem1265202 (n : nat) (m : nat) : (term130 m n) = (term131 n m).
Proof. exact (fun_ext (fun p : nat => @lem1265201 n m p)). Qed.
Lemma lem1265203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1265204 (n : nat) (m : nat) : (term132 m n) = (term133 n m).
Proof. exact (MK_COMB (@lem1265203) (@lem1265202 n m)). Qed.
Lemma lem1265205 (m : nat) : (term134 m) = (term135 m).
Proof. exact (fun_ext (fun n : nat => @lem1265204 n m)). Qed.
Lemma lem1265206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1265207 (m : nat) : (term136 m) = (term137 m).
Proof. exact (MK_COMB (@lem1265206) (@lem1265205 m)). Qed.
Lemma lem1265208 : term138 = term139.
Proof. exact (fun_ext (fun m : nat => @lem1265207 m)). Qed.
Lemma lem1265209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1265210 : term140 = term141.
Proof. exact (MK_COMB (@lem1265209) (@lem1265208)). Qed.
Lemma lem1265211 : term141.
Proof. exact (EQ_MP (@lem1265210) (@lem104208)). Qed.
Lemma lem1265220 (a : Prop) : term142 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1265221 (a : Prop) : (term142 a) = (term143 a).
Proof. exact (eq_refl (term142 a)). Qed.
Lemma lem1265222 (a : Prop) : term143 a.
Proof. exact (EQ_MP (@lem1265221 a) (@lem1265220 a)). Qed.
Lemma lem1265223 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1265224 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1265233 (b : Prop) : (term144 b) = (term144 b).
Proof. exact (eq_refl (term144 b)). Qed.
Lemma lem1265234 (b : Prop) (a : Prop) (h1 : a = True) : (term145 b a) = (term146 b).
Proof. exact (MK_COMB (@lem1265233 b) (@lem1265223 a h1)). Qed.
Lemma lem1265235 (b : Prop) : (term146 b) = ((term147 b) = (True \/ b)).
Proof. exact (eq_refl (term146 b)). Qed.
Lemma lem1265236 (b : Prop) (a : Prop) : (term148 b a) = (term148 b a).
Proof. exact (eq_refl (term148 b a)). Qed.
Lemma lem1265237 (a : Prop) (b : Prop) : ((term145 b a) = (term146 b)) = ((term145 b a) = ((term147 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem1265236 b a) (@lem1265235 b)). Qed.
Lemma lem1265238 (a : Prop) (b : Prop) : (term145 b a) = ((term149 a b) = (a \/ b)).
Proof. exact (eq_refl (term145 b a)). Qed.
Lemma lem1265239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1265240 (a : Prop) (b : Prop) : (term148 b a) = (term150 a b).
Proof. exact (MK_COMB (@lem1265239) (@lem1265238 a b)). Qed.
Lemma lem1265241 (b : Prop) : ((term147 b) = (True \/ b)) = ((term147 b) = (True \/ b)).
Proof. exact (eq_refl ((term147 b) = (True \/ b))). Qed.
Lemma lem1265242 (a : Prop) (b : Prop) : ((term145 b a) = ((term147 b) = (True \/ b))) = (((term149 a b) = (a \/ b)) = ((term147 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem1265240 a b) (@lem1265241 b)). Qed.
Lemma lem1265243 (a : Prop) (b : Prop) : ((term145 b a) = (term146 b)) = (((term149 a b) = (a \/ b)) = ((term147 b) = (True \/ b))).
Proof. exact (TRANS (@lem1265237 a b) (@lem1265242 a b)). Qed.
Lemma lem1265244 (b : Prop) (a : Prop) (h1 : a = True) : ((term149 a b) = (a \/ b)) = ((term147 b) = (True \/ b)).
Proof. exact (EQ_MP (@lem1265243 a b) (@lem1265234 b a h1)). Qed.
Lemma lem1265245 (b : Prop) (a : Prop) (h1 : a = True) : ((term147 b) = (True \/ b)) = ((term149 a b) = (a \/ b)).
Proof. exact (SYM (@lem1265244 b a h1)). Qed.
Lemma lem1265246 (b : Prop) : (term144 b) = (term144 b).
Proof. exact (eq_refl (term144 b)). Qed.
Lemma lem1265247 (b : Prop) (a : Prop) (h1 : a = False) : (term145 b a) = (term151 b).
Proof. exact (MK_COMB (@lem1265246 b) (@lem1265224 a h1)). Qed.
Lemma lem1265248 (b : Prop) : (term151 b) = ((term152 b) = (False \/ b)).
Proof. exact (eq_refl (term151 b)). Qed.
Lemma lem1265249 (b : Prop) (a : Prop) : (term148 b a) = (term148 b a).
Proof. exact (eq_refl (term148 b a)). Qed.
Lemma lem1265250 (a : Prop) (b : Prop) : ((term145 b a) = (term151 b)) = ((term145 b a) = ((term152 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem1265249 b a) (@lem1265248 b)). Qed.
Lemma lem1265251 (a : Prop) (b : Prop) : (term145 b a) = ((term149 a b) = (a \/ b)).
Proof. exact (eq_refl (term145 b a)). Qed.
Lemma lem1265252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1265253 (a : Prop) (b : Prop) : (term148 b a) = (term150 a b).
Proof. exact (MK_COMB (@lem1265252) (@lem1265251 a b)). Qed.
Lemma lem1265254 (b : Prop) : ((term152 b) = (False \/ b)) = ((term152 b) = (False \/ b)).
Proof. exact (eq_refl ((term152 b) = (False \/ b))). Qed.
Lemma lem1265255 (a : Prop) (b : Prop) : ((term145 b a) = ((term152 b) = (False \/ b))) = (((term149 a b) = (a \/ b)) = ((term152 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem1265253 a b) (@lem1265254 b)). Qed.
Lemma lem1265256 (a : Prop) (b : Prop) : ((term145 b a) = (term151 b)) = (((term149 a b) = (a \/ b)) = ((term152 b) = (False \/ b))).
Proof. exact (TRANS (@lem1265250 a b) (@lem1265255 a b)). Qed.
Lemma lem1265257 (b : Prop) (a : Prop) (h1 : a = False) : ((term149 a b) = (a \/ b)) = ((term152 b) = (False \/ b)).
Proof. exact (EQ_MP (@lem1265256 a b) (@lem1265247 b a h1)). Qed.
Lemma lem1265258 (b : Prop) (a : Prop) (h1 : a = False) : ((term152 b) = (False \/ b)) = ((term149 a b) = (a \/ b)).
Proof. exact (SYM (@lem1265257 b a h1)). Qed.
Lemma lem1265264 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1265265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1265266 : term153 = (imp False).
Proof. exact (MK_COMB (@lem1265265) (@lem1265264)). Qed.
Lemma lem1265267 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1265268 (b : Prop) : (term147 b) = (False -> b).
Proof. exact (MK_COMB (@lem1265266) (@lem1265267 b)). Qed.
Lemma lem1265270 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1265271 (b : Prop) : (False -> b) = True.
Proof. exact (@lem1265270 b). Qed.
Lemma lem1265272 (b : Prop) : (term147 b) = True.
Proof. exact (TRANS (@lem1265268 b) (@lem1265271 b)). Qed.
Lemma lem1265273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1265274 (b : Prop) : (term154 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1265273) (@lem1265272 b)). Qed.
Lemma lem1265276 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1265277 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem1265276 b). Qed.
Lemma lem1265278 (b : Prop) : ((term147 b) = (True \/ b)) = (True = True).
Proof. exact (MK_COMB (@lem1265274 b) (@lem1265277 b)). Qed.
Lemma lem1265280 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1265281 : (True = True) = True.
Proof. exact (@lem1265280 True). Qed.
Lemma lem1265282 (b : Prop) : ((term147 b) = (True \/ b)) = True.
Proof. exact (TRANS (@lem1265278 b) (@lem1265281)). Qed.
Lemma lem1265283 (b : Prop) : True = ((term147 b) = (True \/ b)).
Proof. exact (SYM (@lem1265282 b)). Qed.
Lemma lem1265284 (b : Prop) : (term147 b) = (True \/ b).
Proof. exact (EQ_MP (@lem1265283 b) (@lem0)). Qed.
Lemma lem1265290 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1265291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1265292 : term155 = (imp True).
Proof. exact (MK_COMB (@lem1265291) (@lem1265290)). Qed.
Lemma lem1265293 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1265294 (b : Prop) : (term152 b) = (True -> b).
Proof. exact (MK_COMB (@lem1265292) (@lem1265293 b)). Qed.
Lemma lem1265296 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1265297 (b : Prop) : (True -> b) = b.
Proof. exact (@lem1265296 b). Qed.
Lemma lem1265298 (b : Prop) : (term152 b) = b.
Proof. exact (TRANS (@lem1265294 b) (@lem1265297 b)). Qed.
Lemma lem1265299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1265300 (b : Prop) : (term156 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem1265299) (@lem1265298 b)). Qed.
Lemma lem1265302 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1265303 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem1265302 b). Qed.
Lemma lem1265304 (b : Prop) : ((term152 b) = (False \/ b)) = (b = b).
Proof. exact (MK_COMB (@lem1265300 b) (@lem1265303 b)). Qed.
Lemma lem1265306 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1265307 (x : Prop) : (x = x) = True.
Proof. exact (@lem1265306 Prop x). Qed.
Lemma lem1265308 (b : Prop) : (b = b) = True.
Proof. exact (@lem1265307 b). Qed.
Lemma lem1265309 (b : Prop) : ((term152 b) = (False \/ b)) = True.
Proof. exact (TRANS (@lem1265304 b) (@lem1265308 b)). Qed.
Lemma lem1265310 (b : Prop) : True = ((term152 b) = (False \/ b)).
Proof. exact (SYM (@lem1265309 b)). Qed.
Lemma lem1265311 (b : Prop) : (term152 b) = (False \/ b).
Proof. exact (EQ_MP (@lem1265310 b) (@lem0)). Qed.
Lemma lem1265312 (b : Prop) (a : Prop) (h1 : a = False) : (term149 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem1265258 b a h1) (@lem1265311 b)). Qed.
Lemma lem1265313 (b : Prop) (a : Prop) (h1 : a = True) : (term149 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem1265245 b a h1) (@lem1265284 b)). Qed.
Lemma lem1265317 (m : nat) : term157 m.
Proof. exact (@lem1265211 m). Qed.
Lemma lem1265318 (m : nat) : (term157 m) = (term137 m).
Proof. exact (eq_refl (term157 m)). Qed.
Lemma lem1265319 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1265318 m) (@lem1265317 m)). Qed.
Lemma lem1265320 (m : nat) (n : nat) : term158 m n.
Proof. exact (@lem1265319 m n). Qed.
Lemma lem1265321 (n : nat) (m : nat) : (term158 m n) = (term133 n m).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem1265322 (n : nat) (m : nat) : term133 n m.
Proof. exact (EQ_MP (@lem1265321 n m) (@lem1265320 m n)). Qed.
Lemma lem1265323 (n : nat) (m : nat) (p : nat) : term159 n m p.
Proof. exact (@lem1265322 n m p). Qed.
Lemma lem1265324 (n : nat) (m : nat) (p : nat) : (term159 n m p) = ((term129 m n p) = (term128 n m p)).
Proof. exact (eq_refl (term159 n m p)). Qed.
Lemma lem1265326 (m : nat) : term160 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1265327 (m : nat) : (term160 m) = (term161 m).
Proof. exact (eq_refl (term160 m)). Qed.
Lemma lem1265328 (m : nat) : term161 m.
Proof. exact (EQ_MP (@lem1265327 m) (@lem1265326 m)). Qed.
Lemma lem1265329 (m : nat) (n : nat) : term162 m n.
Proof. exact (@lem1265328 m n). Qed.
Lemma lem1265330 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem1265331 (m : nat) (n : nat) : term163 m n.
Proof. exact (EQ_MP (@lem1265330 m n) (@lem1265329 m n)). Qed.
Lemma lem1265332 (m : nat) (n : nat) : (term163 m n) = ((term163 m n) = True).
Proof. exact (@lem7 (term163 m n)). Qed.
Lemma lem1265334 (h1 : term164) : term164.
Proof. exact (h1). Qed.
Lemma lem1265335 (m : nat) (h1 : term164) : term165 m.
Proof. exact (@lem1265334 h1 m). Qed.
Lemma lem1265336 (m : nat) : (term165 m) = (term166 m).
Proof. exact (eq_refl (term165 m)). Qed.
Lemma lem1265337 (m : nat) (h1 : term164) : term166 m.
Proof. exact (EQ_MP (@lem1265336 m) (@lem1265335 m h1)). Qed.
Lemma lem1265338 (m : nat) (n : nat) (h1 : term164) : term167 m n.
Proof. exact (@lem1265337 m h1 n). Qed.
Lemma lem1265339 (n : nat) (m : nat) : (term167 m n) = (term168 n m).
Proof. exact (eq_refl (term167 m n)). Qed.
Lemma lem1265340 (n : nat) (m : nat) (h1 : term164) : term168 n m.
Proof. exact (EQ_MP (@lem1265339 n m) (@lem1265338 m n h1)). Qed.
Lemma lem1265341 (n : nat) (m : nat) (p : nat) (h1 : term164) : term169 n m p.
Proof. exact (@lem1265340 n m h1 p). Qed.
Lemma lem1265342 (n : nat) (m : nat) (p : nat) : (term169 n m p) = (term170 n m p).
Proof. exact (eq_refl (term169 n m p)). Qed.
Lemma lem1265343 (n : nat) (m : nat) (p : nat) (h1 : term164) : term170 n m p.
Proof. exact (EQ_MP (@lem1265342 n m p) (@lem1265341 n m p h1)). Qed.
Lemma lem1265344 (m : nat) (n : nat) (p : nat) (h1 : term171 m n p) : term171 m n p.
Proof. exact (h1). Qed.
Lemma lem1265345 (m : nat) (n : nat) (p : nat) (h1 : term164) (h2 : term171 m n p) : Peano.le m p.
Proof. exact (@lem1265343 n m p h1 (@lem1265344 m n p h2)). Qed.
Lemma lem1265346 (m : nat) (n : nat) (p : nat) (h1 : term171 m n p) : term172 m p.
Proof. exact (fun h0 : term164 => @lem1265345 m n p h0 h1). Qed.
Lemma lem1265347 (m : nat) (p : nat) (h1 : term173 m p) : term173 m p.
Proof. exact (h1). Qed.
Lemma lem1265348 (m : nat) (p : nat) (h1 : term173 m p) : term172 m p.
Proof. exact (ex_elim (@lem1265347 m p h1) (fun n : nat => fun h0 : term174 m p n => @lem1265346 m n p h0)). Qed.
Lemma lem1265349 (h1 : term164) : term164.
Proof. exact (h1). Qed.
Lemma lem1265350 (m : nat) (p : nat) (h1 : term164) (h2 : term173 m p) : Peano.le m p.
Proof. exact (@lem1265348 m p h2 (@lem1265349 h1)). Qed.
Lemma lem1265351 (m : nat) (p : nat) (h1 : term164) : term175 m p.
Proof. exact (fun h0 : term173 m p => @lem1265350 m p h1 h0). Qed.
Lemma lem1265352 (m : nat) (h1 : term164) : term176 m.
Proof. exact (fun p : nat => @lem1265351 m p h1). Qed.
Lemma lem1265353 (h1 : term164) : term177.
Proof. exact (fun m : nat => @lem1265352 m h1). Qed.
Lemma lem1265354 : term178.
Proof. exact (fun h0 : term164 => @lem1265353 h0). Qed.
Lemma lem1265355 : term177.
Proof. exact (@lem1265354 (@lem93743)). Qed.
Lemma lem1265356 (m : nat) : term179 m.
Proof. exact (@lem1265355 m). Qed.
Lemma lem1265357 (m : nat) : (term179 m) = (term176 m).
Proof. exact (eq_refl (term179 m)). Qed.
Lemma lem1265358 (m : nat) : term176 m.
Proof. exact (EQ_MP (@lem1265357 m) (@lem1265356 m)). Qed.
Lemma lem1265359 (m : nat) (p : nat) : term180 m p.
Proof. exact (@lem1265358 m p). Qed.
Lemma lem1265360 (m : nat) (p : nat) : (term180 m p) = (term175 m p).
Proof. exact (eq_refl (term180 m p)). Qed.
Lemma lem1265362 (m : nat) : term181 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1265363 (m : nat) : (term181 m) = (term182 m).
Proof. exact (eq_refl (term181 m)). Qed.
Lemma lem1265364 (m : nat) : term182 m.
Proof. exact (EQ_MP (@lem1265363 m) (@lem1265362 m)). Qed.
Lemma lem1265365 (m : nat) (n : nat) : term183 m n.
Proof. exact (@lem1265364 m n). Qed.
Lemma lem1265366 (n : nat) (m : nat) : (term183 m n) = ((term184 m n) = (term184 n m)).
Proof. exact (eq_refl (term183 m n)). Qed.
Lemma lem1265368 (m : nat) : term185 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1265369 (m : nat) : (term185 m) = (term186 m).
Proof. exact (eq_refl (term185 m)). Qed.
Lemma lem1265370 (m : nat) : term186 m.
Proof. exact (EQ_MP (@lem1265369 m) (@lem1265368 m)). Qed.
Lemma lem1265371 (m : nat) (n : nat) : term187 m n.
Proof. exact (@lem1265370 m n). Qed.
Lemma lem1265372 (m : nat) (n : nat) : (term187 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term188 m n)).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem1265374 (m : nat) (n : nat) : term189 m n.
Proof. exact (@lem9784 ((Nat.add m n) = (NUMERAL 0))). Qed.
Lemma lem1265375 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (eq_refl (term189 m n)). Qed.
Lemma lem1265376 (m : nat) (n : nat) : term190 m n.
Proof. exact (EQ_MP (@lem1265375 m n) (@lem1265374 m n)). Qed.
Lemma lem1265377 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1265378 (m : nat) (n : nat) (h1 : term191 m n) : term191 m n.
Proof. exact (h1). Qed.
Lemma lem1265379 (x : nadd) : term192 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1265380 (x : nadd) : (term192 x) = (term193 x).
Proof. exact (eq_refl (term192 x)). Qed.
Lemma lem1265381 (x : nadd) : term193 x.
Proof. exact (EQ_MP (@lem1265380 x) (@lem1265379 x)). Qed.
Lemma lem1265382 (x : nadd) (B : nat) (h1 : term194 x B) : term194 x B.
Proof. exact (h1). Qed.
Lemma lem1265394 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term188 m n).
Proof. exact (EQ_MP (@lem1265372 m n) (@lem1265371 m n)). Qed.
Lemma lem1265401 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : term188 m n.
Proof. exact (EQ_MP (@lem1265394 m n) (@lem1265377 m n h1)). Qed.
Lemma lem1265403 (n : nat) (m : nat) : (term184 m n) = (term184 n m).
Proof. exact (EQ_MP (@lem1265366 n m) (@lem1265365 m n)). Qed.
Lemma lem1265404 (x : nadd) (m : nat) (n : nat) : (term195 m x n) = (term196 x m n).
Proof. exact (@lem1265403 (term197 m x n) (term198 x m n)). Qed.
Lemma lem1265405 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1265406 (x : nadd) (m : nat) (n : nat) : (term199 m x n) = (term200 x m n).
Proof. exact (MK_COMB (@lem1265405) (@lem1265404 x m n)). Qed.
Lemma lem1265407 (B : nat) (x : nadd) : (term201 B x) = (term201 B x).
Proof. exact (eq_refl (term201 B x)). Qed.
Lemma lem1265408 (m : nat) (n : nat) (B : nat) (x : nadd) : (term202 m n B x) = (term203 m n B x).
Proof. exact (MK_COMB (@lem1265406 x m n) (@lem1265407 B x)). Qed.
Lemma lem1265409 (m : nat) (n : nat) (B : nat) (x : nadd) : (term203 m n B x) = (term202 m n B x).
Proof. exact (SYM (@lem1265408 m n B x)). Qed.
Lemma lem1265410 (m : nat) : term204 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1265411 (m : nat) : (term204 m) = (term205 m).
Proof. exact (eq_refl (term204 m)). Qed.
Lemma lem1265412 (m : nat) : term205 m.
Proof. exact (EQ_MP (@lem1265411 m) (@lem1265410 m)). Qed.
Lemma lem1265413 (m : nat) (n : nat) : term206 m n.
Proof. exact (@lem1265412 m n). Qed.
Lemma lem1265414 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem1265415 (m : nat) (n : nat) : term207 m n.
Proof. exact (EQ_MP (@lem1265414 m n) (@lem1265413 m n)). Qed.
Lemma lem1265416 (m : nat) (n : nat) : (term207 m n) = ((term207 m n) = True).
Proof. exact (@lem7 (term207 m n)). Qed.
Lemma lem1265418 (m : nat) : term208 m.
Proof. exact (@lem1245246 m). Qed.
Lemma lem1265419 (m : nat) : (term208 m) = (term209 m).
Proof. exact (eq_refl (term208 m)). Qed.
Lemma lem1265420 (m : nat) : term209 m.
Proof. exact (EQ_MP (@lem1265419 m) (@lem1265418 m)). Qed.
Lemma lem1265421 (m : nat) (n : nat) : term210 m n.
Proof. exact (@lem1265420 m n). Qed.
Lemma lem1265422 (m : nat) (n : nat) : (term210 m n) = ((term211 n m) = n).
Proof. exact (eq_refl (term210 m n)). Qed.
Lemma lem1265444 : term212.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1265445 (n : nat) : term213 n.
Proof. exact (@lem1265444 n). Qed.
Lemma lem1265446 (n : nat) : (term213 n) = ((term214 n) = n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem1265463 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (proj1 (@lem1265401 m n h1)). Qed.
Lemma lem1265464 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1265465 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (dest_nadd x m) = (term215 x).
Proof. exact (MK_COMB (@lem1265464 x) (@lem1265463 m n h1)). Qed.
Lemma lem1265466 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265467 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term216 x m) = (term217 x).
Proof. exact (MK_COMB (@lem1265466) (@lem1265465 x m n h1)). Qed.
Lemma lem1265469 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (proj2 (@lem1265401 m n h1)). Qed.
Lemma lem1265470 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1265471 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (dest_nadd x n) = (term215 x).
Proof. exact (MK_COMB (@lem1265470 x) (@lem1265469 m n h1)). Qed.
Lemma lem1265472 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term197 m x n) = (term218 x).
Proof. exact (MK_COMB (@lem1265467 x m n h1) (@lem1265471 x m n h1)). Qed.
Lemma lem1265473 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1265474 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term219 m x n) = (term220 x).
Proof. exact (MK_COMB (@lem1265473) (@lem1265472 x m n h1)). Qed.
Lemma lem1265476 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (proj1 (@lem1265401 m n h1)). Qed.
Lemma lem1265477 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265478 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m) = term221.
Proof. exact (MK_COMB (@lem1265477) (@lem1265476 m n h1)). Qed.
Lemma lem1265480 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (proj2 (@lem1265401 m n h1)). Qed.
Lemma lem1265481 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = term222.
Proof. exact (MK_COMB (@lem1265478 m n h1) (@lem1265480 m n h1)). Qed.
Lemma lem1265483 (n : nat) : (term214 n) = n.
Proof. exact (EQ_MP (@lem1265446 n) (@lem1265445 n)). Qed.
Lemma lem1265484 : term222 = (NUMERAL 0).
Proof. exact (@lem1265483 (NUMERAL 0)). Qed.
Lemma lem1265485 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1265481 m n h1) (@lem1265484)). Qed.
Lemma lem1265486 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1265487 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term198 x m n) = (term215 x).
Proof. exact (MK_COMB (@lem1265486 x) (@lem1265485 m n h1)). Qed.
Lemma lem1265488 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term223 x m n) = (term224 x).
Proof. exact (MK_COMB (@lem1265474 x m n h1) (@lem1265487 x m n h1)). Qed.
Lemma lem1265489 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1265490 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term196 x m n) = (term225 x).
Proof. exact (MK_COMB (@lem1265489) (@lem1265488 x m n h1)). Qed.
Lemma lem1265492 (m : nat) (n : nat) : (term211 n m) = n.
Proof. exact (EQ_MP (@lem1265422 m n) (@lem1265421 m n)). Qed.
Lemma lem1265493 (x : nadd) : (term225 x) = (term215 x).
Proof. exact (@lem1265492 (term215 x) (term215 x)). Qed.
Lemma lem1265494 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term196 x m n) = (term215 x).
Proof. exact (TRANS (@lem1265490 x m n h1) (@lem1265493 x)). Qed.
Lemma lem1265495 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1265496 (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term200 x m n) = (term226 x).
Proof. exact (MK_COMB (@lem1265495) (@lem1265494 x m n h1)). Qed.
Lemma lem1265497 (B : nat) (x : nadd) : (term201 B x) = (term201 B x).
Proof. exact (eq_refl (term201 B x)). Qed.
Lemma lem1265498 (B : nat) (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term203 m n B x) = (term227 B x).
Proof. exact (MK_COMB (@lem1265496 x m n h1) (@lem1265497 B x)). Qed.
Lemma lem1265500 (m : nat) (n : nat) : (term207 m n) = True.
Proof. exact (EQ_MP (@lem1265416 m n) (@lem1265415 m n)). Qed.
Lemma lem1265501 (B : nat) (x : nadd) : (term227 B x) = True.
Proof. exact (@lem1265500 (term228 B) (term215 x)). Qed.
Lemma lem1265502 (B : nat) (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (term203 m n B x) = True.
Proof. exact (TRANS (@lem1265498 B x m n h1) (@lem1265501 B x)). Qed.
Lemma lem1265503 (B : nat) (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : True = (term203 m n B x).
Proof. exact (SYM (@lem1265502 B x m n h1)). Qed.
Lemma lem1265504 (B : nat) (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : term203 m n B x.
Proof. exact (EQ_MP (@lem1265503 B x m n h1) (@lem0)). Qed.
Lemma lem1265505 (B : nat) (x : nadd) (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : term202 m n B x.
Proof. exact (EQ_MP (@lem1265409 m n B x) (@lem1265504 B x m n h1)). Qed.
Lemma lem1265507 (m : nat) (p : nat) : term175 m p.
Proof. exact (EQ_MP (@lem1265360 m p) (@lem1265359 m p)). Qed.
Lemma lem1265508 (m : nat) (n : nat) (B : nat) (x : nadd) : term229 m n B x.
Proof. exact (@lem1265507 (term195 m x n) (term201 B x)). Qed.
Lemma lem1265512 (m : nat) (n : nat) : (term163 m n) = True.
Proof. exact (EQ_MP (@lem1265332 m n) (@lem1265331 m n)). Qed.
Lemma lem1265513 (B : nat) (x : nadd) : (term230 B x) = True.
Proof. exact (@lem1265512 (term228 B) (term215 x)). Qed.
Lemma lem1265514 (m : nat) (x : nadd) (n : nat) (B : nat) : (term231 m x n B) = (term231 m x n B).
Proof. exact (eq_refl (term231 m x n B)). Qed.
Lemma lem1265515 (m : nat) (x : nadd) (n : nat) (B : nat) : (term232 m n B x) = (term233 m x n B).
Proof. exact (MK_COMB (@lem1265514 m x n B) (@lem1265513 B x)). Qed.
Lemma lem1265517 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1265518 (m : nat) (x : nadd) (n : nat) (B : nat) : (term233 m x n B) = (term234 m x n B).
Proof. exact (@lem1265517 (term234 m x n B)). Qed.
Lemma lem1265519 (m : nat) (x : nadd) (n : nat) (B : nat) : (term232 m n B x) = (term234 m x n B).
Proof. exact (TRANS (@lem1265515 m x n B) (@lem1265518 m x n B)). Qed.
Lemma lem1265520 (m : nat) (n : nat) (B : nat) (x : nadd) : (term234 m x n B) = (term232 m n B x).
Proof. exact (SYM (@lem1265519 m x n B)). Qed.
Lemma lem1265522 (a : Prop) (b : Prop) : (term149 a b) = (a \/ b).
Proof. exact (or_elim (@lem1265222 a) (fun h0 : a = True => @lem1265313 b a h0) (fun h0 : a = False => @lem1265312 b a h0)). Qed.
Lemma lem1265523 (m : nat) (x : nadd) (n : nat) (B : nat) : (term235 m x n B) = (term236 m x n B).
Proof. exact (@lem1265522 ((Nat.add m n) = (NUMERAL 0)) (term234 m x n B)). Qed.
Lemma lem1265525 (n : nat) (m : nat) (p : nat) : (term129 m n p) = (term128 n m p).
Proof. exact (EQ_MP (@lem1265324 n m p) (@lem1265323 n m p)). Qed.
Lemma lem1265526 (x : nadd) (m : nat) (n : nat) (B : nat) : (term236 m x n B) = (term237 x m n B).
Proof. exact (@lem1265525 (term195 m x n) (Nat.add m n) (term228 B)). Qed.
Lemma lem1265527 (x : nadd) (m : nat) (n : nat) (B : nat) : (term235 m x n B) = (term237 x m n B).
Proof. exact (TRANS (@lem1265523 m x n B) (@lem1265526 x m n B)). Qed.
Lemma lem1265528 (m : nat) (x : nadd) (n : nat) (B : nat) : (term237 x m n B) = (term235 m x n B).
Proof. exact (SYM (@lem1265527 x m n B)). Qed.
Lemma lem1265530 (n : nat) (m : nat) (p : nat) : (term126 m n p) = (term127 n m p).
Proof. exact (EQ_MP (@lem1265192 n m p) (@lem1265191 n m p)). Qed.
Lemma lem1265531 (m : nat) (x : nadd) (n : nat) : (term238 m x n) = (term239 m x n).
Proof. exact (@lem1265530 (term198 x m n) (Nat.add m n) (term197 m x n)). Qed.
Lemma lem1265533 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1265183 n m p) (@lem1265182 n m p)). Qed.
Lemma lem1265534 (m : nat) (x : nadd) (n : nat) : (term240 m x n) = (term241 m x n).
Proof. exact (@lem1265533 (dest_nadd x m) (Nat.add m n) (dest_nadd x n)). Qed.
Lemma lem1265535 (x : nadd) (m : nat) (n : nat) : (term242 x m n) = (term242 x m n).
Proof. exact (eq_refl (term242 x m n)). Qed.
Lemma lem1265536 (m : nat) (x : nadd) (n : nat) : (term243 m x n) = (term244 m x n).
Proof. exact (MK_COMB (@lem1265535 x m n) (@lem1265534 m x n)). Qed.
Lemma lem1265537 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1265538 (m : nat) (x : nadd) (n : nat) : (term239 m x n) = (term245 m x n).
Proof. exact (MK_COMB (@lem1265537) (@lem1265536 m x n)). Qed.
Lemma lem1265539 (m : nat) (x : nadd) (n : nat) : (term238 m x n) = (term245 m x n).
Proof. exact (TRANS (@lem1265531 m x n) (@lem1265538 m x n)). Qed.
Lemma lem1265540 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1265541 (m : nat) (x : nadd) (n : nat) : (term246 m x n) = (term247 m x n).
Proof. exact (MK_COMB (@lem1265540) (@lem1265539 m x n)). Qed.
Lemma lem1265542 (m : nat) (n : nat) (B : nat) : (term248 m n B) = (term248 m n B).
Proof. exact (eq_refl (term248 m n B)). Qed.
Lemma lem1265543 (x : nadd) (m : nat) (n : nat) (B : nat) : (term237 x m n B) = (term249 x m n B).
Proof. exact (MK_COMB (@lem1265541 m x n) (@lem1265542 m n B)). Qed.
Lemma lem1265544 (x : nadd) (m : nat) (n : nat) (B : nat) : (term249 x m n B) = (term237 x m n B).
Proof. exact (SYM (@lem1265543 x m n B)). Qed.
Lemma lem1265546 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1265174 m n p) (@lem1265173 m n p)). Qed.
Lemma lem1265547 (x : nadd) (m : nat) (n : nat) : (term250 x m n) = (term251 x m n).
Proof. exact (@lem1265546 m n (term198 x m n)). Qed.
Lemma lem1265548 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1265549 (x : nadd) (m : nat) (n : nat) : (term242 x m n) = (term252 x m n).
Proof. exact (MK_COMB (@lem1265548) (@lem1265547 x m n)). Qed.
Lemma lem1265550 (m : nat) (x : nadd) (n : nat) : (term241 m x n) = (term241 m x n).
Proof. exact (eq_refl (term241 m x n)). Qed.
Lemma lem1265551 (m : nat) (x : nadd) (n : nat) : (term244 m x n) = (term253 m x n).
Proof. exact (MK_COMB (@lem1265549 x m n) (@lem1265550 m x n)). Qed.
Lemma lem1265552 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1265553 (m : nat) (x : nadd) (n : nat) : (term245 m x n) = (term254 m x n).
Proof. exact (MK_COMB (@lem1265552) (@lem1265551 m x n)). Qed.
Lemma lem1265554 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1265555 (m : nat) (x : nadd) (n : nat) : (term247 m x n) = (term255 m x n).
Proof. exact (MK_COMB (@lem1265554) (@lem1265553 m x n)). Qed.
Lemma lem1265556 (m : nat) (n : nat) (B : nat) : (term248 m n B) = (term248 m n B).
Proof. exact (eq_refl (term248 m n B)). Qed.
Lemma lem1265557 (x : nadd) (m : nat) (n : nat) (B : nat) : (term249 x m n B) = (term256 x m n B).
Proof. exact (MK_COMB (@lem1265555 m x n) (@lem1265556 m n B)). Qed.
Lemma lem1265558 (x : nadd) (m : nat) (n : nat) (B : nat) : (term256 x m n B) = (term249 x m n B).
Proof. exact (SYM (@lem1265557 x m n B)). Qed.
Lemma lem1265560 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term116 m n p q p'.
Proof. exact (EQ_MP (@lem1265165 m n p q p') (@lem1265164 m n p q p')). Qed.
Lemma lem1265561 (x : nadd) (m : nat) (n : nat) (B : nat) : term257 x m n B.
Proof. exact (@lem1265560 (term258 x m n) (term259 x m n) (term260 n x m) (term261 m x n) (term248 m n B)). Qed.
Lemma lem1265562 (B : nat) (m : nat) (n : nat) (h1 : (term248 m n B) = (term262 B m n)) : (term248 m n B) = (term262 B m n).
Proof. exact (h1). Qed.
Lemma lem1265563 (m : nat) (x : nadd) (n : nat) : (term263 m x n) = (term263 m x n).
Proof. exact (eq_refl (term263 m x n)). Qed.
Lemma lem1265564 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : (term248 m n B) = (term262 B m n)) : (term264 x m n B) = (term265 x B m n).
Proof. exact (MK_COMB (@lem1265563 m x n) (@lem1265562 B m n h1)). Qed.
Lemma lem1265565 (x : nadd) (B : nat) (m : nat) (n : nat) : (term265 x B m n) = (term266 x B m n).
Proof. exact (eq_refl (term265 x B m n)). Qed.
Lemma lem1265566 (x : nadd) (m : nat) (n : nat) (B : nat) : (term267 x m n B) = (term267 x m n B).
Proof. exact (eq_refl (term267 x m n B)). Qed.
Lemma lem1265567 (x : nadd) (B : nat) (m : nat) (n : nat) : ((term264 x m n B) = (term265 x B m n)) = ((term264 x m n B) = (term266 x B m n)).
Proof. exact (MK_COMB (@lem1265566 x m n B) (@lem1265565 x B m n)). Qed.
Lemma lem1265568 (x : nadd) (m : nat) (n : nat) (B : nat) : (term264 x m n B) = (term268 x m n B).
Proof. exact (eq_refl (term264 x m n B)). Qed.
Lemma lem1265569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1265570 (x : nadd) (m : nat) (n : nat) (B : nat) : (term267 x m n B) = (term269 x m n B).
Proof. exact (MK_COMB (@lem1265569) (@lem1265568 x m n B)). Qed.
Lemma lem1265571 (x : nadd) (B : nat) (m : nat) (n : nat) : (term266 x B m n) = (term266 x B m n).
Proof. exact (eq_refl (term266 x B m n)). Qed.
Lemma lem1265572 (x : nadd) (B : nat) (m : nat) (n : nat) : ((term264 x m n B) = (term266 x B m n)) = ((term268 x m n B) = (term266 x B m n)).
Proof. exact (MK_COMB (@lem1265570 x m n B) (@lem1265571 x B m n)). Qed.
Lemma lem1265573 (x : nadd) (B : nat) (m : nat) (n : nat) : ((term264 x m n B) = (term265 x B m n)) = ((term268 x m n B) = (term266 x B m n)).
Proof. exact (TRANS (@lem1265567 x B m n) (@lem1265572 x B m n)). Qed.
Lemma lem1265574 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : (term248 m n B) = (term262 B m n)) : (term268 x m n B) = (term266 x B m n).
Proof. exact (EQ_MP (@lem1265573 x B m n) (@lem1265564 x B m n h1)). Qed.
Lemma lem1265575 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : (term248 m n B) = (term262 B m n)) : (term266 x B m n) = (term268 x m n B).
Proof. exact (SYM (@lem1265574 x B m n h1)). Qed.
Lemma lem1265579 : term79 = term72.
Proof. exact (SYM (@lem1265077)). Qed.
Lemma lem1265580 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1265581 : term270 = term271.
Proof. exact (MK_COMB (@lem1265580) (@lem1265579)). Qed.
Lemma lem1265582 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1265583 (B : nat) : (term228 B) = (term272 B).
Proof. exact (MK_COMB (@lem1265581) (@lem1265582 B)). Qed.
Lemma lem1265584 (m : nat) (n : nat) : (term273 m n) = (term273 m n).
Proof. exact (eq_refl (term273 m n)). Qed.
Lemma lem1265585 (m : nat) (n : nat) (B : nat) : (term248 m n B) = (term274 m n B).
Proof. exact (MK_COMB (@lem1265584 m n) (@lem1265583 B)). Qed.
Lemma lem1265586 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1265587 (m : nat) (n : nat) (B : nat) : (term275 m n B) = (term276 m n B).
Proof. exact (MK_COMB (@lem1265586) (@lem1265585 m n B)). Qed.
Lemma lem1265588 (B : nat) (m : nat) (n : nat) : (term262 B m n) = (term262 B m n).
Proof. exact (eq_refl (term262 B m n)). Qed.
Lemma lem1265589 (B : nat) (m : nat) (n : nat) : ((term248 m n B) = (term262 B m n)) = ((term274 m n B) = (term262 B m n)).
Proof. exact (MK_COMB (@lem1265587 m n B) (@lem1265588 B m n)). Qed.
Lemma lem1265592 (B : nat) (m : nat) (n : nat) : ((term274 m n B) = (term262 B m n)) = ((term248 m n B) = (term262 B m n)).
Proof. exact (SYM (@lem1265589 B m n)). Qed.
Lemma lem1265596 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1264395 m n p) (@lem1264394 m n p)). Qed.
Lemma lem1265597 (m : nat) (n : nat) (B : nat) : (term274 m n B) = (term277 m n B).
Proof. exact (@lem1265596 m n (term272 B)). Qed.
Lemma lem1265599 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1264395 m n p) (@lem1264394 m n p)). Qed.
Lemma lem1265600 (B : nat) : (term272 B) = (term278 B).
Proof. exact (@lem1265599 term279 term64 B). Qed.
Lemma lem1265602 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265603 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265602 B). Qed.
Lemma lem1265604 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265605 (B : nat) : (term280 B) = (Nat.add B).
Proof. exact (MK_COMB (@lem1265604) (@lem1265603 B)). Qed.
Lemma lem1265607 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1264395 m n p) (@lem1264394 m n p)). Qed.
Lemma lem1265608 (B : nat) : (term281 B) = (term282 B).
Proof. exact (@lem1265607 term279 term279 B). Qed.
Lemma lem1265610 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265611 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265610 B). Qed.
Lemma lem1265612 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265613 (B : nat) : (term280 B) = (Nat.add B).
Proof. exact (MK_COMB (@lem1265612) (@lem1265611 B)). Qed.
Lemma lem1265615 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265616 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265615 B). Qed.
Lemma lem1265617 (B : nat) : (term282 B) = (Nat.add B B).
Proof. exact (MK_COMB (@lem1265613 B) (@lem1265616 B)). Qed.
Lemma lem1265618 (B : nat) : (term281 B) = (Nat.add B B).
Proof. exact (TRANS (@lem1265608 B) (@lem1265617 B)). Qed.
Lemma lem1265619 (B : nat) : (term278 B) = (term283 B).
Proof. exact (MK_COMB (@lem1265605 B) (@lem1265618 B)). Qed.
Lemma lem1265620 (B : nat) : (term272 B) = (term283 B).
Proof. exact (TRANS (@lem1265600 B) (@lem1265619 B)). Qed.
Lemma lem1265621 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1265622 (m : nat) (B : nat) : (term284 m B) = (term285 m B).
Proof. exact (MK_COMB (@lem1265621 m) (@lem1265620 B)). Qed.
Lemma lem1265624 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265625 (m : nat) (B : nat) : (term285 m B) = (term286 m B).
Proof. exact (@lem1265624 B m (Nat.add B B)). Qed.
Lemma lem1265627 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265628 (m : nat) (B : nat) : (term287 m B) = (term288 m B).
Proof. exact (@lem1265627 B m B). Qed.
Lemma lem1265629 (m : nat) (B : nat) : (term289 m B) = (term289 m B).
Proof. exact (eq_refl (term289 m B)). Qed.
Lemma lem1265630 (m : nat) (B : nat) : (term286 m B) = (term290 m B).
Proof. exact (MK_COMB (@lem1265629 m B) (@lem1265628 m B)). Qed.
Lemma lem1265631 (m : nat) (B : nat) : (term285 m B) = (term290 m B).
Proof. exact (TRANS (@lem1265625 m B) (@lem1265630 m B)). Qed.
Lemma lem1265632 (m : nat) (B : nat) : (term284 m B) = (term290 m B).
Proof. exact (TRANS (@lem1265622 m B) (@lem1265631 m B)). Qed.
Lemma lem1265633 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265634 (m : nat) (B : nat) : (term291 m B) = (term292 m B).
Proof. exact (MK_COMB (@lem1265633) (@lem1265632 m B)). Qed.
Lemma lem1265636 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1264395 m n p) (@lem1264394 m n p)). Qed.
Lemma lem1265637 (B : nat) : (term272 B) = (term278 B).
Proof. exact (@lem1265636 term279 term64 B). Qed.
Lemma lem1265639 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265640 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265639 B). Qed.
Lemma lem1265641 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265642 (B : nat) : (term280 B) = (Nat.add B).
Proof. exact (MK_COMB (@lem1265641) (@lem1265640 B)). Qed.
Lemma lem1265644 (m : nat) (n : nat) (p : nat) : (term30 m n p) = (term31 m n p).
Proof. exact (EQ_MP (@lem1264395 m n p) (@lem1264394 m n p)). Qed.
Lemma lem1265645 (B : nat) : (term281 B) = (term282 B).
Proof. exact (@lem1265644 term279 term279 B). Qed.
Lemma lem1265647 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265648 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265647 B). Qed.
Lemma lem1265649 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265650 (B : nat) : (term280 B) = (Nat.add B).
Proof. exact (MK_COMB (@lem1265649) (@lem1265648 B)). Qed.
Lemma lem1265652 (n : nat) : (term17 n) = n.
Proof. exact (EQ_MP (@lem1264369 n) (@lem1264368 n)). Qed.
Lemma lem1265653 (B : nat) : (term17 B) = B.
Proof. exact (@lem1265652 B). Qed.
Lemma lem1265654 (B : nat) : (term282 B) = (Nat.add B B).
Proof. exact (MK_COMB (@lem1265650 B) (@lem1265653 B)). Qed.
Lemma lem1265655 (B : nat) : (term281 B) = (Nat.add B B).
Proof. exact (TRANS (@lem1265645 B) (@lem1265654 B)). Qed.
Lemma lem1265656 (B : nat) : (term278 B) = (term283 B).
Proof. exact (MK_COMB (@lem1265642 B) (@lem1265655 B)). Qed.
Lemma lem1265657 (B : nat) : (term272 B) = (term283 B).
Proof. exact (TRANS (@lem1265637 B) (@lem1265656 B)). Qed.
Lemma lem1265658 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1265659 (n : nat) (B : nat) : (term284 n B) = (term285 n B).
Proof. exact (MK_COMB (@lem1265658 n) (@lem1265657 B)). Qed.
Lemma lem1265661 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265662 (n : nat) (B : nat) : (term285 n B) = (term286 n B).
Proof. exact (@lem1265661 B n (Nat.add B B)). Qed.
Lemma lem1265664 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265665 (n : nat) (B : nat) : (term287 n B) = (term288 n B).
Proof. exact (@lem1265664 B n B). Qed.
Lemma lem1265666 (n : nat) (B : nat) : (term289 n B) = (term289 n B).
Proof. exact (eq_refl (term289 n B)). Qed.
Lemma lem1265667 (n : nat) (B : nat) : (term286 n B) = (term290 n B).
Proof. exact (MK_COMB (@lem1265666 n B) (@lem1265665 n B)). Qed.
Lemma lem1265668 (n : nat) (B : nat) : (term285 n B) = (term290 n B).
Proof. exact (TRANS (@lem1265662 n B) (@lem1265667 n B)). Qed.
Lemma lem1265669 (n : nat) (B : nat) : (term284 n B) = (term290 n B).
Proof. exact (TRANS (@lem1265659 n B) (@lem1265668 n B)). Qed.
Lemma lem1265670 (m : nat) (n : nat) (B : nat) : (term277 m n B) = (term293 m n B).
Proof. exact (MK_COMB (@lem1265634 m B) (@lem1265669 n B)). Qed.
Lemma lem1265671 (m : nat) (n : nat) (B : nat) : (term274 m n B) = (term293 m n B).
Proof. exact (TRANS (@lem1265597 m n B) (@lem1265670 m n B)). Qed.
Lemma lem1265672 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1265673 (m : nat) (n : nat) (B : nat) : (term276 m n B) = (term294 m n B).
Proof. exact (MK_COMB (@lem1265672) (@lem1265671 m n B)). Qed.
Lemma lem1265675 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265676 (B : nat) (m : nat) (n : nat) : (term295 B m n) = (term296 B m n).
Proof. exact (@lem1265675 m B (Nat.add m n)). Qed.
Lemma lem1265678 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265679 (m : nat) (B : nat) (n : nat) : (term23 B m n) = (term24 m B n).
Proof. exact (@lem1265678 m B n). Qed.
Lemma lem1265680 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265681 (m : nat) (B : nat) (n : nat) : (term296 B m n) = (term297 m B n).
Proof. exact (MK_COMB (@lem1265680 B m) (@lem1265679 m B n)). Qed.
Lemma lem1265682 (m : nat) (B : nat) (n : nat) : (term295 B m n) = (term297 m B n).
Proof. exact (TRANS (@lem1265676 B m n) (@lem1265681 m B n)). Qed.
Lemma lem1265683 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265684 (m : nat) (B : nat) (n : nat) : (term298 B m n) = (term299 m B n).
Proof. exact (MK_COMB (@lem1265683) (@lem1265682 m B n)). Qed.
Lemma lem1265686 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265687 (B : nat) (m : nat) (n : nat) : (term300 B m n) = (term301 B m n).
Proof. exact (@lem1265686 n B (Nat.add m n)). Qed.
Lemma lem1265689 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1264386 n m p) (@lem1264385 n m p)). Qed.
Lemma lem1265690 (m : nat) (B : nat) (n : nat) : (term23 B m n) = (term24 m B n).
Proof. exact (@lem1265689 m B n). Qed.
Lemma lem1265691 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1265692 (m : nat) (B : nat) (n : nat) : (term301 B m n) = (term302 m B n).
Proof. exact (MK_COMB (@lem1265691 B n) (@lem1265690 m B n)). Qed.
Lemma lem1265693 (m : nat) (B : nat) (n : nat) : (term300 B m n) = (term302 m B n).
Proof. exact (TRANS (@lem1265687 B m n) (@lem1265692 m B n)). Qed.
Lemma lem1265694 (m : nat) (B : nat) (n : nat) : (term262 B m n) = (term303 m B n).
Proof. exact (MK_COMB (@lem1265684 m B n) (@lem1265693 m B n)). Qed.
Lemma lem1265695 (m : nat) (B : nat) (n : nat) : ((term274 m n B) = (term262 B m n)) = ((term293 m n B) = (term303 m B n)).
Proof. exact (MK_COMB (@lem1265673 m n B) (@lem1265694 m B n)). Qed.
Lemma lem1265698 (B : nat) (m : nat) (n : nat) : ((term293 m n B) = (term303 m B n)) = ((term274 m n B) = (term262 B m n)).
Proof. exact (SYM (@lem1265695 m B n)). Qed.
Lemma lem1265702 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265703 (B : nat) (m : nat) : (Nat.mul m B) = (Nat.mul B m).
Proof. exact (@lem1265702 B m). Qed.
Lemma lem1265707 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265708 (B : nat) (m : nat) : (term289 m B) = (term289 B m).
Proof. exact (MK_COMB (@lem1265707) (@lem1265703 B m)). Qed.
Lemma lem1265710 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265711 (B : nat) (m : nat) : (Nat.mul m B) = (Nat.mul B m).
Proof. exact (@lem1265710 B m). Qed.
Lemma lem1265715 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265716 (B : nat) (m : nat) : (term289 m B) = (term289 B m).
Proof. exact (MK_COMB (@lem1265715) (@lem1265711 B m)). Qed.
Lemma lem1265718 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265719 (B : nat) (m : nat) : (Nat.mul m B) = (Nat.mul B m).
Proof. exact (@lem1265718 B m). Qed.
Lemma lem1265723 (B : nat) (m : nat) : (term288 m B) = (term288 B m).
Proof. exact (MK_COMB (@lem1265716 B m) (@lem1265719 B m)). Qed.
Lemma lem1265724 (B : nat) (m : nat) : (term290 m B) = (term290 B m).
Proof. exact (MK_COMB (@lem1265708 B m) (@lem1265723 B m)). Qed.
Lemma lem1265725 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265726 (B : nat) (m : nat) : (term292 m B) = (term292 B m).
Proof. exact (MK_COMB (@lem1265725) (@lem1265724 B m)). Qed.
Lemma lem1265728 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265729 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1265728 B n). Qed.
Lemma lem1265733 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265734 (B : nat) (n : nat) : (term289 n B) = (term289 B n).
Proof. exact (MK_COMB (@lem1265733) (@lem1265729 B n)). Qed.
Lemma lem1265736 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265737 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1265736 B n). Qed.
Lemma lem1265741 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1265742 (B : nat) (n : nat) : (term289 n B) = (term289 B n).
Proof. exact (MK_COMB (@lem1265741) (@lem1265737 B n)). Qed.
Lemma lem1265744 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1265745 (B : nat) (n : nat) : (Nat.mul n B) = (Nat.mul B n).
Proof. exact (@lem1265744 B n). Qed.
Lemma lem1265749 (B : nat) (n : nat) : (term288 n B) = (term288 B n).
Proof. exact (MK_COMB (@lem1265742 B n) (@lem1265745 B n)). Qed.
Lemma lem1265750 (B : nat) (n : nat) : (term290 n B) = (term290 B n).
Proof. exact (MK_COMB (@lem1265734 B n) (@lem1265749 B n)). Qed.
Lemma lem1265751 (m : nat) (B : nat) (n : nat) : (term293 m n B) = (term304 m B n).
Proof. exact (MK_COMB (@lem1265726 B m) (@lem1265750 B n)). Qed.
Lemma lem1265752 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1265753 (m : nat) (B : nat) (n : nat) : (term294 m n B) = (term305 m B n).
Proof. exact (MK_COMB (@lem1265752) (@lem1265751 m B n)). Qed.
Lemma lem1265772 (m : nat) (B : nat) (n : nat) : (term303 m B n) = (term303 m B n).
Proof. exact (eq_refl (term303 m B n)). Qed.
Lemma lem1265773 (m : nat) (B : nat) (n : nat) : ((term293 m n B) = (term303 m B n)) = ((term304 m B n) = (term303 m B n)).
Proof. exact (MK_COMB (@lem1265753 m B n) (@lem1265772 m B n)). Qed.
Lemma lem1265776 (m : nat) (B : nat) (n : nat) : ((term304 m B n) = (term303 m B n)) = ((term293 m n B) = (term303 m B n)).
Proof. exact (SYM (@lem1265773 m B n)). Qed.
Lemma lem1265780 (m : nat) (n : nat) (p : nat) : (term306 m n p) = (term307 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1265781 (m : nat) (B : nat) (n : nat) : (term304 m B n) = (term308 m B n).
Proof. exact (@lem1265780 (Nat.mul B m) (term288 B m) (term290 B n)). Qed.
Lemma lem1265789 (m : nat) (n : nat) (p : nat) : (term306 m n p) = (term307 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1265790 (m : nat) (B : nat) (n : nat) : (term309 m B n) = (term310 m B n).
Proof. exact (@lem1265789 (Nat.mul B m) (Nat.mul B m) (term290 B n)). Qed.
Lemma lem1265812 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265813 (m : nat) (B : nat) (n : nat) : (term308 m B n) = (term311 m B n).
Proof. exact (MK_COMB (@lem1265812 B m) (@lem1265790 m B n)). Qed.
Lemma lem1265820 (m : nat) (B : nat) (n : nat) : (term304 m B n) = (term311 m B n).
Proof. exact (TRANS (@lem1265781 m B n) (@lem1265813 m B n)). Qed.
Lemma lem1265821 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1265822 (m : nat) (B : nat) (n : nat) : (term305 m B n) = (term312 m B n).
Proof. exact (MK_COMB (@lem1265821) (@lem1265820 m B n)). Qed.
Lemma lem1265836 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265837 (n : nat) (B : nat) (m : nat) : (term313 n B m) = (term314 n B m).
Proof. exact (@lem1265836 (Nat.mul B m) (Nat.mul B n) (term288 B m)). Qed.
Lemma lem1265845 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265846 (n : nat) (B : nat) (m : nat) : (term315 n B m) = (term302 n B m).
Proof. exact (@lem1265845 (Nat.mul B m) (Nat.mul B n) (Nat.mul B m)). Qed.
Lemma lem1265854 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1265855 (m : nat) (B : nat) (n : nat) : (term24 n B m) = (term24 m B n).
Proof. exact (@lem1265854 (Nat.mul B m) (Nat.mul B n)). Qed.
Lemma lem1265859 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265860 (m : nat) (B : nat) (n : nat) : (term302 n B m) = (term297 m B n).
Proof. exact (MK_COMB (@lem1265859 B m) (@lem1265855 m B n)). Qed.
Lemma lem1265867 (m : nat) (B : nat) (n : nat) : (term315 n B m) = (term297 m B n).
Proof. exact (TRANS (@lem1265846 n B m) (@lem1265860 m B n)). Qed.
Lemma lem1265868 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265869 (m : nat) (B : nat) (n : nat) : (term314 n B m) = (term316 m B n).
Proof. exact (MK_COMB (@lem1265868 B m) (@lem1265867 m B n)). Qed.
Lemma lem1265876 (m : nat) (B : nat) (n : nat) : (term313 n B m) = (term316 m B n).
Proof. exact (TRANS (@lem1265837 n B m) (@lem1265869 m B n)). Qed.
Lemma lem1265877 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1265878 (m : nat) (B : nat) (n : nat) : (term310 n B m) = (term317 m B n).
Proof. exact (MK_COMB (@lem1265877 B n) (@lem1265876 m B n)). Qed.
Lemma lem1265880 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265881 (m : nat) (B : nat) (n : nat) : (term317 m B n) = (term318 m B n).
Proof. exact (@lem1265880 (Nat.mul B m) (Nat.mul B n) (term297 m B n)). Qed.
Lemma lem1265889 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265890 (m : nat) (B : nat) (n : nat) : (term319 m B n) = (term320 m B n).
Proof. exact (@lem1265889 (Nat.mul B m) (Nat.mul B n) (term24 m B n)). Qed.
Lemma lem1265898 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265899 (m : nat) (B : nat) (n : nat) : (term302 m B n) = (term315 m B n).
Proof. exact (@lem1265898 (Nat.mul B m) (Nat.mul B n) (Nat.mul B n)). Qed.
Lemma lem1265909 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265910 (m : nat) (B : nat) (n : nat) : (term320 m B n) = (term321 m B n).
Proof. exact (MK_COMB (@lem1265909 B m) (@lem1265899 m B n)). Qed.
Lemma lem1265917 (m : nat) (B : nat) (n : nat) : (term319 m B n) = (term321 m B n).
Proof. exact (TRANS (@lem1265890 m B n) (@lem1265910 m B n)). Qed.
Lemma lem1265918 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265919 (m : nat) (B : nat) (n : nat) : (term318 m B n) = (term322 m B n).
Proof. exact (MK_COMB (@lem1265918 B m) (@lem1265917 m B n)). Qed.
Lemma lem1265926 (m : nat) (B : nat) (n : nat) : (term317 m B n) = (term322 m B n).
Proof. exact (TRANS (@lem1265881 m B n) (@lem1265919 m B n)). Qed.
Lemma lem1265927 (m : nat) (B : nat) (n : nat) : (term310 n B m) = (term322 m B n).
Proof. exact (TRANS (@lem1265878 m B n) (@lem1265926 m B n)). Qed.
Lemma lem1265928 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1265929 (m : nat) (B : nat) (n : nat) : (term311 n B m) = (term323 m B n).
Proof. exact (MK_COMB (@lem1265928 B n) (@lem1265927 m B n)). Qed.
Lemma lem1265931 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265932 (m : nat) (B : nat) (n : nat) : (term323 m B n) = (term324 m B n).
Proof. exact (@lem1265931 (Nat.mul B m) (Nat.mul B n) (term321 m B n)). Qed.
Lemma lem1265940 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265941 (m : nat) (B : nat) (n : nat) : (term325 m B n) = (term326 m B n).
Proof. exact (@lem1265940 (Nat.mul B m) (Nat.mul B n) (term315 m B n)). Qed.
Lemma lem1265949 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1265950 (m : nat) (B : nat) (n : nat) : (term314 m B n) = (term313 m B n).
Proof. exact (@lem1265949 (Nat.mul B m) (Nat.mul B n) (term288 B n)). Qed.
Lemma lem1265966 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265967 (m : nat) (B : nat) (n : nat) : (term326 m B n) = (term310 m B n).
Proof. exact (MK_COMB (@lem1265966 B m) (@lem1265950 m B n)). Qed.
Lemma lem1265974 (m : nat) (B : nat) (n : nat) : (term325 m B n) = (term310 m B n).
Proof. exact (TRANS (@lem1265941 m B n) (@lem1265967 m B n)). Qed.
Lemma lem1265975 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1265976 (m : nat) (B : nat) (n : nat) : (term324 m B n) = (term311 m B n).
Proof. exact (MK_COMB (@lem1265975 B m) (@lem1265974 m B n)). Qed.
Lemma lem1265983 (m : nat) (B : nat) (n : nat) : (term323 m B n) = (term311 m B n).
Proof. exact (TRANS (@lem1265932 m B n) (@lem1265976 m B n)). Qed.
Lemma lem1265984 (m : nat) (B : nat) (n : nat) : (term311 n B m) = (term311 m B n).
Proof. exact (TRANS (@lem1265929 m B n) (@lem1265983 m B n)). Qed.
Lemma lem1265985 (m : nat) (B : nat) (n : nat) : ((term304 m B n) = (term311 n B m)) = ((term311 m B n) = (term311 m B n)).
Proof. exact (MK_COMB (@lem1265822 m B n) (@lem1265984 m B n)). Qed.
Lemma lem1265987 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1265988 (x : nat) : (x = x) = True.
Proof. exact (@lem1265987 nat x). Qed.
Lemma lem1265989 (m : nat) (B : nat) (n : nat) : ((term311 m B n) = (term311 m B n)) = True.
Proof. exact (@lem1265988 (term311 m B n)). Qed.
Lemma lem1265990 (n : nat) (B : nat) (m : nat) : ((term304 m B n) = (term311 n B m)) = True.
Proof. exact (TRANS (@lem1265985 m B n) (@lem1265989 m B n)). Qed.
Lemma lem1265991 (n : nat) (B : nat) (m : nat) : True = ((term304 m B n) = (term311 n B m)).
Proof. exact (SYM (@lem1265990 n B m)). Qed.
Lemma lem1265992 (n : nat) (B : nat) (m : nat) : (term304 m B n) = (term311 n B m).
Proof. exact (EQ_MP (@lem1265991 n B m) (@lem0)). Qed.
Lemma lem1265996 (m : nat) (n : nat) (p : nat) : (term306 m n p) = (term307 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1265997 (m : nat) (B : nat) (n : nat) : (term303 m B n) = (term327 m B n).
Proof. exact (@lem1265996 (Nat.mul B m) (term24 m B n) (term302 m B n)). Qed.
Lemma lem1266005 (m : nat) (n : nat) (p : nat) : (term306 m n p) = (term307 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1266006 (m : nat) (B : nat) (n : nat) : (term328 m B n) = (term329 m B n).
Proof. exact (@lem1266005 (Nat.mul B m) (Nat.mul B n) (term302 m B n)). Qed.
Lemma lem1266020 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266021 (m : nat) (B : nat) (n : nat) : (term302 m B n) = (term315 m B n).
Proof. exact (@lem1266020 (Nat.mul B m) (Nat.mul B n) (Nat.mul B n)). Qed.
Lemma lem1266031 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1266032 (m : nat) (B : nat) (n : nat) : (term330 m B n) = (term314 m B n).
Proof. exact (MK_COMB (@lem1266031 B n) (@lem1266021 m B n)). Qed.
Lemma lem1266034 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266035 (m : nat) (B : nat) (n : nat) : (term314 m B n) = (term313 m B n).
Proof. exact (@lem1266034 (Nat.mul B m) (Nat.mul B n) (term288 B n)). Qed.
Lemma lem1266051 (m : nat) (B : nat) (n : nat) : (term330 m B n) = (term313 m B n).
Proof. exact (TRANS (@lem1266032 m B n) (@lem1266035 m B n)). Qed.
Lemma lem1266052 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266053 (m : nat) (B : nat) (n : nat) : (term329 m B n) = (term310 m B n).
Proof. exact (MK_COMB (@lem1266052 B m) (@lem1266051 m B n)). Qed.
Lemma lem1266060 (m : nat) (B : nat) (n : nat) : (term328 m B n) = (term310 m B n).
Proof. exact (TRANS (@lem1266006 m B n) (@lem1266053 m B n)). Qed.
Lemma lem1266061 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266062 (m : nat) (B : nat) (n : nat) : (term327 m B n) = (term311 m B n).
Proof. exact (MK_COMB (@lem1266061 B m) (@lem1266060 m B n)). Qed.
Lemma lem1266069 (m : nat) (B : nat) (n : nat) : (term303 m B n) = (term311 m B n).
Proof. exact (TRANS (@lem1265997 m B n) (@lem1266062 m B n)). Qed.
Lemma lem1266070 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1266071 (m : nat) (B : nat) (n : nat) : (term331 m B n) = (term312 m B n).
Proof. exact (MK_COMB (@lem1266070) (@lem1266069 m B n)). Qed.
Lemma lem1266085 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266086 (n : nat) (B : nat) (m : nat) : (term313 n B m) = (term314 n B m).
Proof. exact (@lem1266085 (Nat.mul B m) (Nat.mul B n) (term288 B m)). Qed.
Lemma lem1266094 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266095 (n : nat) (B : nat) (m : nat) : (term315 n B m) = (term302 n B m).
Proof. exact (@lem1266094 (Nat.mul B m) (Nat.mul B n) (Nat.mul B m)). Qed.
Lemma lem1266103 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1266104 (m : nat) (B : nat) (n : nat) : (term24 n B m) = (term24 m B n).
Proof. exact (@lem1266103 (Nat.mul B m) (Nat.mul B n)). Qed.
Lemma lem1266108 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266109 (m : nat) (B : nat) (n : nat) : (term302 n B m) = (term297 m B n).
Proof. exact (MK_COMB (@lem1266108 B m) (@lem1266104 m B n)). Qed.
Lemma lem1266116 (m : nat) (B : nat) (n : nat) : (term315 n B m) = (term297 m B n).
Proof. exact (TRANS (@lem1266095 n B m) (@lem1266109 m B n)). Qed.
Lemma lem1266117 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266118 (m : nat) (B : nat) (n : nat) : (term314 n B m) = (term316 m B n).
Proof. exact (MK_COMB (@lem1266117 B m) (@lem1266116 m B n)). Qed.
Lemma lem1266125 (m : nat) (B : nat) (n : nat) : (term313 n B m) = (term316 m B n).
Proof. exact (TRANS (@lem1266086 n B m) (@lem1266118 m B n)). Qed.
Lemma lem1266126 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1266127 (m : nat) (B : nat) (n : nat) : (term310 n B m) = (term317 m B n).
Proof. exact (MK_COMB (@lem1266126 B n) (@lem1266125 m B n)). Qed.
Lemma lem1266129 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266130 (m : nat) (B : nat) (n : nat) : (term317 m B n) = (term318 m B n).
Proof. exact (@lem1266129 (Nat.mul B m) (Nat.mul B n) (term297 m B n)). Qed.
Lemma lem1266138 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266139 (m : nat) (B : nat) (n : nat) : (term319 m B n) = (term320 m B n).
Proof. exact (@lem1266138 (Nat.mul B m) (Nat.mul B n) (term24 m B n)). Qed.
Lemma lem1266147 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266148 (m : nat) (B : nat) (n : nat) : (term302 m B n) = (term315 m B n).
Proof. exact (@lem1266147 (Nat.mul B m) (Nat.mul B n) (Nat.mul B n)). Qed.
Lemma lem1266158 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266159 (m : nat) (B : nat) (n : nat) : (term320 m B n) = (term321 m B n).
Proof. exact (MK_COMB (@lem1266158 B m) (@lem1266148 m B n)). Qed.
Lemma lem1266166 (m : nat) (B : nat) (n : nat) : (term319 m B n) = (term321 m B n).
Proof. exact (TRANS (@lem1266139 m B n) (@lem1266159 m B n)). Qed.
Lemma lem1266167 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266168 (m : nat) (B : nat) (n : nat) : (term318 m B n) = (term322 m B n).
Proof. exact (MK_COMB (@lem1266167 B m) (@lem1266166 m B n)). Qed.
Lemma lem1266175 (m : nat) (B : nat) (n : nat) : (term317 m B n) = (term322 m B n).
Proof. exact (TRANS (@lem1266130 m B n) (@lem1266168 m B n)). Qed.
Lemma lem1266176 (m : nat) (B : nat) (n : nat) : (term310 n B m) = (term322 m B n).
Proof. exact (TRANS (@lem1266127 m B n) (@lem1266175 m B n)). Qed.
Lemma lem1266177 (B : nat) (n : nat) : (term289 B n) = (term289 B n).
Proof. exact (eq_refl (term289 B n)). Qed.
Lemma lem1266178 (m : nat) (B : nat) (n : nat) : (term311 n B m) = (term323 m B n).
Proof. exact (MK_COMB (@lem1266177 B n) (@lem1266176 m B n)). Qed.
Lemma lem1266180 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266181 (m : nat) (B : nat) (n : nat) : (term323 m B n) = (term324 m B n).
Proof. exact (@lem1266180 (Nat.mul B m) (Nat.mul B n) (term321 m B n)). Qed.
Lemma lem1266189 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266190 (m : nat) (B : nat) (n : nat) : (term325 m B n) = (term326 m B n).
Proof. exact (@lem1266189 (Nat.mul B m) (Nat.mul B n) (term315 m B n)). Qed.
Lemma lem1266198 (n : nat) (m : nat) (p : nat) : (term307 m n p) = (term307 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1266199 (m : nat) (B : nat) (n : nat) : (term314 m B n) = (term313 m B n).
Proof. exact (@lem1266198 (Nat.mul B m) (Nat.mul B n) (term288 B n)). Qed.
Lemma lem1266215 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266216 (m : nat) (B : nat) (n : nat) : (term326 m B n) = (term310 m B n).
Proof. exact (MK_COMB (@lem1266215 B m) (@lem1266199 m B n)). Qed.
Lemma lem1266223 (m : nat) (B : nat) (n : nat) : (term325 m B n) = (term310 m B n).
Proof. exact (TRANS (@lem1266190 m B n) (@lem1266216 m B n)). Qed.
Lemma lem1266224 (B : nat) (m : nat) : (term289 B m) = (term289 B m).
Proof. exact (eq_refl (term289 B m)). Qed.
Lemma lem1266225 (m : nat) (B : nat) (n : nat) : (term324 m B n) = (term311 m B n).
Proof. exact (MK_COMB (@lem1266224 B m) (@lem1266223 m B n)). Qed.
Lemma lem1266232 (m : nat) (B : nat) (n : nat) : (term323 m B n) = (term311 m B n).
Proof. exact (TRANS (@lem1266181 m B n) (@lem1266225 m B n)). Qed.
Lemma lem1266233 (m : nat) (B : nat) (n : nat) : (term311 n B m) = (term311 m B n).
Proof. exact (TRANS (@lem1266178 m B n) (@lem1266232 m B n)). Qed.
Lemma lem1266234 (m : nat) (B : nat) (n : nat) : ((term303 m B n) = (term311 n B m)) = ((term311 m B n) = (term311 m B n)).
Proof. exact (MK_COMB (@lem1266071 m B n) (@lem1266233 m B n)). Qed.
Lemma lem1266236 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1266237 (x : nat) : (x = x) = True.
Proof. exact (@lem1266236 nat x). Qed.
Lemma lem1266238 (m : nat) (B : nat) (n : nat) : ((term311 m B n) = (term311 m B n)) = True.
Proof. exact (@lem1266237 (term311 m B n)). Qed.
Lemma lem1266239 (n : nat) (B : nat) (m : nat) : ((term303 m B n) = (term311 n B m)) = True.
Proof. exact (TRANS (@lem1266234 m B n) (@lem1266238 m B n)). Qed.
Lemma lem1266240 (n : nat) (B : nat) (m : nat) : True = ((term303 m B n) = (term311 n B m)).
Proof. exact (SYM (@lem1266239 n B m)). Qed.
Lemma lem1266241 (n : nat) (B : nat) (m : nat) : (term303 m B n) = (term311 n B m).
Proof. exact (EQ_MP (@lem1266240 n B m) (@lem0)). Qed.
Lemma lem1266242 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1266243 (n : nat) (B : nat) (m : nat) : (term305 m B n) = (term312 n B m).
Proof. exact (MK_COMB (@lem1266242) (@lem1265992 n B m)). Qed.
Lemma lem1266244 (n : nat) (B : nat) (m : nat) : ((term304 m B n) = (term303 m B n)) = ((term311 n B m) = (term311 n B m)).
Proof. exact (MK_COMB (@lem1266243 n B m) (@lem1266241 n B m)). Qed.
Lemma lem1266257 (m : nat) : term332 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1266258 (m : nat) : (term332 m) = (term333 m).
Proof. exact (eq_refl (term332 m)). Qed.
Lemma lem1266259 (m : nat) : term333 m.
Proof. exact (EQ_MP (@lem1266258 m) (@lem1266257 m)). Qed.
Lemma lem1266260 (m : nat) (n : nat) : term334 m n.
Proof. exact (@lem1266259 m n). Qed.
Lemma lem1266261 (m : nat) (n : nat) : (term334 m n) = (term335 m n).
Proof. exact (eq_refl (term334 m n)). Qed.
Lemma lem1266262 (m : nat) (n : nat) : term335 m n.
Proof. exact (EQ_MP (@lem1266261 m n) (@lem1266260 m n)). Qed.
Lemma lem1266263 (m : nat) (n : nat) (p : nat) : term336 m n p.
Proof. exact (@lem1266262 m n p). Qed.
Lemma lem1266264 (m : nat) (n : nat) (p : nat) : (term336 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term336 m n p)). Qed.
Lemma lem1266267 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1266264 m n p) (@lem1266263 m n p)). Qed.
Lemma lem1266268 (n : nat) (B : nat) (m : nat) : ((term311 n B m) = (term311 n B m)) = ((term310 n B m) = (term310 n B m)).
Proof. exact (@lem1266267 (Nat.mul B n) (term310 n B m) (term310 n B m)). Qed.
Lemma lem1266270 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1266264 m n p) (@lem1266263 m n p)). Qed.
Lemma lem1266271 (n : nat) (B : nat) (m : nat) : ((term310 n B m) = (term310 n B m)) = ((term313 n B m) = (term313 n B m)).
Proof. exact (@lem1266270 (Nat.mul B n) (term313 n B m) (term313 n B m)). Qed.
Lemma lem1266273 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1266264 m n p) (@lem1266263 m n p)). Qed.
Lemma lem1266274 (n : nat) (B : nat) (m : nat) : ((term313 n B m) = (term313 n B m)) = ((term290 B m) = (term290 B m)).
Proof. exact (@lem1266273 (Nat.mul B n) (term290 B m) (term290 B m)). Qed.
Lemma lem1266276 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1266264 m n p) (@lem1266263 m n p)). Qed.
Lemma lem1266277 (B : nat) (m : nat) : ((term290 B m) = (term290 B m)) = ((term288 B m) = (term288 B m)).
Proof. exact (@lem1266276 (Nat.mul B m) (term288 B m) (term288 B m)). Qed.
Lemma lem1266279 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1266264 m n p) (@lem1266263 m n p)). Qed.
Lemma lem1266282 (B : nat) (m : nat) : ((term288 B m) = (term288 B m)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (@lem1266279 (Nat.mul B m) (Nat.mul B m) (Nat.mul B m)). Qed.
Lemma lem1266283 (B : nat) (m : nat) : ((term290 B m) = (term290 B m)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (TRANS (@lem1266277 B m) (@lem1266282 B m)). Qed.
Lemma lem1266284 (n : nat) (B : nat) (m : nat) : ((term313 n B m) = (term313 n B m)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (TRANS (@lem1266274 n B m) (@lem1266283 B m)). Qed.
Lemma lem1266285 (n : nat) (B : nat) (m : nat) : ((term310 n B m) = (term310 n B m)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (TRANS (@lem1266271 n B m) (@lem1266284 n B m)). Qed.
Lemma lem1266286 (n : nat) (B : nat) (m : nat) : ((term311 n B m) = (term311 n B m)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (TRANS (@lem1266268 n B m) (@lem1266285 n B m)). Qed.
Lemma lem1266287 (m : nat) (B : nat) (n : nat) : (term337 m B n) = (term337 m B n).
Proof. exact (eq_refl (term337 m B n)). Qed.
Lemma lem1266288 (n : nat) (B : nat) (m : nat) : (((term304 m B n) = (term303 m B n)) = ((term311 n B m) = (term311 n B m))) = (((term304 m B n) = (term303 m B n)) = ((Nat.mul B m) = (Nat.mul B m))).
Proof. exact (MK_COMB (@lem1266287 m B n) (@lem1266286 n B m)). Qed.
Lemma lem1266289 (n : nat) (B : nat) (m : nat) : ((term304 m B n) = (term303 m B n)) = ((Nat.mul B m) = (Nat.mul B m)).
Proof. exact (EQ_MP (@lem1266288 n B m) (@lem1266244 n B m)). Qed.
Lemma lem1266290 (m : nat) (B : nat) (n : nat) : ((Nat.mul B m) = (Nat.mul B m)) = ((term304 m B n) = (term303 m B n)).
Proof. exact (SYM (@lem1266289 n B m)). Qed.
Lemma lem1266291 (B : nat) (m : nat) : (Nat.mul B m) = (Nat.mul B m).
Proof. exact (eq_refl (Nat.mul B m)). Qed.
Lemma lem1266292 (m : nat) (B : nat) (n : nat) : (term304 m B n) = (term303 m B n).
Proof. exact (EQ_MP (@lem1266290 m B n) (@lem1266291 B m)). Qed.
Lemma lem1266293 (m : nat) (B : nat) (n : nat) : (term293 m n B) = (term303 m B n).
Proof. exact (EQ_MP (@lem1265776 m B n) (@lem1266292 m B n)). Qed.
Lemma lem1266294 (B : nat) (m : nat) (n : nat) : (term274 m n B) = (term262 B m n).
Proof. exact (EQ_MP (@lem1265698 B m n) (@lem1266293 m B n)). Qed.
Lemma lem1266295 (B : nat) (m : nat) (n : nat) : (term248 m n B) = (term262 B m n).
Proof. exact (EQ_MP (@lem1265592 B m n) (@lem1266294 B m n)). Qed.
Lemma lem1266297 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem1264339 m n p q) (@lem1264338 m n p q)). Qed.
Lemma lem1266298 (x : nadd) (B : nat) (m : nat) (n : nat) : term338 x B m n.
Proof. exact (@lem1266297 (term339 n x m) (term340 m x n) (term295 B m n) (term300 B m n)). Qed.
Lemma lem1266299 (m : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term341 x B m.
Proof. exact (@lem1265382 x B h1 m). Qed.
Lemma lem1266300 (x : nadd) (B : nat) (m : nat) : (term341 x B m) = (term342 x B m).
Proof. exact (eq_refl (term341 x B m)). Qed.
Lemma lem1266301 (m : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term342 x B m.
Proof. exact (EQ_MP (@lem1266300 x B m) (@lem1266299 m x B h1)). Qed.
Lemma lem1266302 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term343 x B m n.
Proof. exact (@lem1266301 m x B h1 n). Qed.
Lemma lem1266303 (x : nadd) (B : nat) (m : nat) (n : nat) : (term343 x B m n) = (term344 x B m n).
Proof. exact (eq_refl (term343 x B m n)). Qed.
Lemma lem1266304 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term344 x B m n.
Proof. exact (EQ_MP (@lem1266303 x B m n) (@lem1266302 m n x B h1)). Qed.
Lemma lem1266305 (x : nadd) (B : nat) (m : nat) (n : nat) : (term344 x B m n) = ((term344 x B m n) = True).
Proof. exact (@lem7 (term344 x B m n)). Qed.
Lemma lem1266310 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term344 x B m n) = True.
Proof. exact (EQ_MP (@lem1266305 x B m n) (@lem1266304 m n x B h1)). Qed.
Lemma lem1266311 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term345 x B m n) = True.
Proof. exact (@lem1266310 m (Nat.add m n) x B h1). Qed.
Lemma lem1266312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1266313 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term346 x B m n) = (and True).
Proof. exact (MK_COMB (@lem1266312) (@lem1266311 m n x B h1)). Qed.
Lemma lem1266315 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term344 x B m n) = True.
Proof. exact (EQ_MP (@lem1266305 x B m n) (@lem1266304 m n x B h1)). Qed.
Lemma lem1266316 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term347 x B m n) = True.
Proof. exact (@lem1266315 n (Nat.add m n) x B h1). Qed.
Lemma lem1266317 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term348 x B m n) = (True /\ True).
Proof. exact (MK_COMB (@lem1266313 m n x B h1) (@lem1266316 m n x B h1)). Qed.
Lemma lem1266319 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1266320 : (True /\ True) = True.
Proof. exact (@lem1266319 True). Qed.
Lemma lem1266321 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : (term348 x B m n) = True.
Proof. exact (TRANS (@lem1266317 m n x B h1) (@lem1266320)). Qed.
Lemma lem1266322 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : True = (term348 x B m n).
Proof. exact (SYM (@lem1266321 m n x B h1)). Qed.
Lemma lem1266323 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term348 x B m n.
Proof. exact (EQ_MP (@lem1266322 m n x B h1) (@lem0)). Qed.
Lemma lem1266324 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term266 x B m n.
Proof. exact (@lem1266298 x B m n (@lem1266323 m n x B h1)). Qed.
Lemma lem1266325 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term194 x B) (h2 : (term248 m n B) = (term262 B m n)) : term268 x m n B.
Proof. exact (EQ_MP (@lem1265575 x B m n h2) (@lem1266324 m n x B h1)). Qed.
Lemma lem1266326 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : ((term248 m n B) = (term262 B m n)) = (term268 x m n B).
Proof. exact (prop_ext (fun h2 : (term248 m n B) = (term262 B m n) => @lem1266325 x B m n h1 h2) (fun h2 : term268 x m n B => @lem1266295 B m n)). Qed.
Lemma lem1266327 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term268 x m n B.
Proof. exact (EQ_MP (@lem1266326 m n x B h1) (@lem1266295 B m n)). Qed.
Lemma lem1266328 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term256 x m n B.
Proof. exact (@lem1265561 x m n B (@lem1266327 m n x B h1)). Qed.
Lemma lem1266329 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term249 x m n B.
Proof. exact (EQ_MP (@lem1265558 x m n B) (@lem1266328 m n x B h1)). Qed.
Lemma lem1266330 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term237 x m n B.
Proof. exact (EQ_MP (@lem1265544 x m n B) (@lem1266329 m n x B h1)). Qed.
Lemma lem1266331 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term235 m x n B.
Proof. exact (EQ_MP (@lem1265528 m x n B) (@lem1266330 m n x B h1)). Qed.
Lemma lem1266332 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term194 x B) (h2 : term191 m n) : term234 m x n B.
Proof. exact (@lem1266331 m n x B h1 (@lem1265378 m n h2)). Qed.
Lemma lem1266333 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term194 x B) (h2 : term191 m n) : term232 m n B x.
Proof. exact (EQ_MP (@lem1265520 m n B x) (@lem1266332 x B m n h1 h2)). Qed.
Lemma lem1266334 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term194 x B) (h2 : term191 m n) : term349 m n B x.
Proof. exact (ex_intro (term350 m n B x) (term228 B) (@lem1266333 x B m n h1 h2)). Qed.
Lemma lem1266335 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term194 x B) (h2 : term191 m n) : term202 m n B x.
Proof. exact (@lem1265508 m n B x (@lem1266334 x B m n h1 h2)). Qed.
Lemma lem1266336 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term202 m n B x.
Proof. exact (or_elim (@lem1265376 m n) (fun h0 : (Nat.add m n) = (NUMERAL 0) => @lem1265505 B x m n h0) (fun h0 : term191 m n => @lem1266335 x B m n h1 h0)). Qed.
Lemma lem1266341 (m : nat) (x : nadd) (B : nat) (h1 : term194 x B) : term351 m B x.
Proof. exact (fun n : nat => @lem1266336 m n x B h1). Qed.
Lemma lem1266346 (x : nadd) (B : nat) (h1 : term194 x B) : term352 B x.
Proof. exact (fun m : nat => @lem1266341 m x B h1). Qed.
Lemma lem1266347 (x : nadd) (B : nat) (h1 : term194 x B) : term353 x.
Proof. exact (ex_intro (term354 x) (term201 B x) (@lem1266346 x B h1)). Qed.
Lemma lem1266348 (x : nadd) : term353 x.
Proof. exact (ex_elim (@lem1265381 x) (fun B : nat => fun h0 : term355 x B => @lem1266347 x B h0)). Qed.
Lemma lem1266353 : term356.
Proof. exact (fun x : nadd => @lem1266348 x). Qed.
