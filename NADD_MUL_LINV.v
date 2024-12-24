Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_term_abbrevs.
Require Import ADD_AC_spec.
Require Import BOUNDS_DIVIDED_spec.
Require Import BOUNDS_IGNORE_spec.
Require Import DIST_LMUL_spec.
Require Import DIST_TRIANGLE_LE_spec.
Require Import LE_ADD2_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_ALTMUL_spec.
Require Import NADD_BOUND_spec.
Require Import NADD_INV_spec.
Require Import NADD_MUL_spec.
Require Import NADD_MUL_LINV_LEMMA2_spec.
Require Import NADD_OF_NUM_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1308249 (m : nat) : term0 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1308250 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1308251 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1308250 m) (@lem1308249 m)). Qed.
Lemma lem1308252 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1308251 m n). Qed.
Lemma lem1308253 (n : nat) (m : nat) : (term2 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1308255 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1308256 (m : nat) (h1 : term3) : term4 m.
Proof. exact (@lem1308255 h1 m). Qed.
Lemma lem1308257 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1308258 (m : nat) (h1 : term3) : term5 m.
Proof. exact (EQ_MP (@lem1308257 m) (@lem1308256 m h1)). Qed.
Lemma lem1308259 (m : nat) (n : nat) (h1 : term3) : term6 m n.
Proof. exact (@lem1308258 m h1 n). Qed.
Lemma lem1308260 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1308261 (m : nat) (n : nat) (h1 : term3) : term7 m n.
Proof. exact (EQ_MP (@lem1308260 m n) (@lem1308259 m n h1)). Qed.
Lemma lem1308262 (m : nat) (n : nat) (p : nat) (h1 : term3) : term8 m n p.
Proof. exact (@lem1308261 m n h1 p). Qed.
Lemma lem1308263 (m : nat) (n : nat) (p : nat) : (term8 m n p) = (term9 m n p).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1308264 (m : nat) (n : nat) (p : nat) (h1 : term3) : term9 m n p.
Proof. exact (EQ_MP (@lem1308263 m n p) (@lem1308262 m n p h1)). Qed.
Lemma lem1308265 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term3) : term10 m n p q.
Proof. exact (@lem1308264 m n p h1 q). Qed.
Lemma lem1308266 (m : nat) (n : nat) (p : nat) (q : nat) : (term10 m n p q) = (term11 m n p q).
Proof. exact (eq_refl (term10 m n p q)). Qed.
Lemma lem1308267 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term3) : term11 m n p q.
Proof. exact (EQ_MP (@lem1308266 m n p q) (@lem1308265 m n p q h1)). Qed.
Lemma lem1308268 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term12 m p n q) : term12 m p n q.
Proof. exact (h1). Qed.
Lemma lem1308269 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term3) (h2 : term12 m p n q) : term13 m n p q.
Proof. exact (@lem1308267 m n p q h1 (@lem1308268 m p n q h2)). Qed.
Lemma lem1308270 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term12 m p n q) : term14 m n p q.
Proof. exact (fun h0 : term3 => @lem1308269 m p n q h0 h1). Qed.
Lemma lem1308271 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1308272 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term3) (h2 : term12 m p n q) : term13 m n p q.
Proof. exact (@lem1308270 m p n q h2 (@lem1308271 h1)). Qed.
Lemma lem1308273 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term3) : term11 m n p q.
Proof. exact (fun h0 : term12 m p n q => @lem1308272 m p n q h1 h0). Qed.
Lemma lem1308274 (m : nat) (n : nat) (p : nat) (h1 : term3) : term9 m n p.
Proof. exact (fun q : nat => @lem1308273 m n p q h1). Qed.
Lemma lem1308275 (m : nat) (n : nat) (h1 : term3) : term7 m n.
Proof. exact (fun p : nat => @lem1308274 m n p h1). Qed.
Lemma lem1308276 (m : nat) (h1 : term3) : term5 m.
Proof. exact (fun n : nat => @lem1308275 m n h1). Qed.
Lemma lem1308277 (h1 : term3) : term3.
Proof. exact (fun m : nat => @lem1308276 m h1). Qed.
Lemma lem1308278 : term15.
Proof. exact (fun h0 : term3 => @lem1308277 h0). Qed.
Lemma lem1308279 : term3.
Proof. exact (@lem1308278 (@lem101399)). Qed.
Lemma lem1308280 (m : nat) : term4 m.
Proof. exact (@lem1308279 m). Qed.
Lemma lem1308281 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1308282 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1308281 m) (@lem1308280 m)). Qed.
Lemma lem1308283 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1308282 m n). Qed.
Lemma lem1308284 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1308285 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1308284 m n) (@lem1308283 m n)). Qed.
Lemma lem1308286 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem1308285 m n p). Qed.
Lemma lem1308287 (m : nat) (n : nat) (p : nat) : (term8 m n p) = (term9 m n p).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1308288 (m : nat) (n : nat) (p : nat) : term9 m n p.
Proof. exact (EQ_MP (@lem1308287 m n p) (@lem1308286 m n p)). Qed.
Lemma lem1308289 (m : nat) (n : nat) (p : nat) (q : nat) : term10 m n p q.
Proof. exact (@lem1308288 m n p q). Qed.
Lemma lem1308290 (m : nat) (n : nat) (p : nat) (q : nat) : (term10 m n p q) = (term11 m n p q).
Proof. exact (eq_refl (term10 m n p q)). Qed.
Lemma lem1308292 {A : Type'} (x : A) : term16 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1308293 {A : Type'} (x : A) : (term16 A x) = ((x = x) = True).
Proof. exact (eq_refl (term16 A x)). Qed.
Lemma lem1308295 (n : nat) (m : nat) (p : nat) : term17 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1308302 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term19 m n p).
Proof. exact (proj1 (@lem1308295 n m p)). Qed.
Lemma lem1308303 (a : nat) (b : nat) (c : nat) (d : nat) : (term20 a b c d) = (term21 a b c d).
Proof. exact (@lem1308302 a b (Nat.add c d)). Qed.
Lemma lem1308319 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1308320 (a : nat) (b : nat) (c : nat) (d : nat) : (term22 a b c d) = (term23 a b c d).
Proof. exact (MK_COMB (@lem1308319) (@lem1308303 a b c d)). Qed.
Lemma lem1308322 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term19 m n p).
Proof. exact (proj1 (@lem1308295 n m p)). Qed.
Lemma lem1308323 (a : nat) (c : nat) (b : nat) (d : nat) : (term20 a c b d) = (term21 a c b d).
Proof. exact (@lem1308322 a c (Nat.add b d)). Qed.
Lemma lem1308331 (n : nat) (m : nat) (p : nat) : (term19 m n p) = (term19 n m p).
Proof. exact (proj2 (@lem1308295 n m p)). Qed.
Lemma lem1308332 (b : nat) (c : nat) (d : nat) : (term19 c b d) = (term19 b c d).
Proof. exact (@lem1308331 b c d). Qed.
Lemma lem1308342 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1308343 (a : nat) (b : nat) (c : nat) (d : nat) : (term21 a c b d) = (term21 a b c d).
Proof. exact (MK_COMB (@lem1308342 a) (@lem1308332 b c d)). Qed.
Lemma lem1308350 (a : nat) (b : nat) (c : nat) (d : nat) : (term20 a c b d) = (term21 a b c d).
Proof. exact (TRANS (@lem1308323 a c b d) (@lem1308343 a b c d)). Qed.
Lemma lem1308351 (a : nat) (b : nat) (c : nat) (d : nat) : ((term20 a b c d) = (term20 a c b d)) = ((term21 a b c d) = (term21 a b c d)).
Proof. exact (MK_COMB (@lem1308320 a b c d) (@lem1308350 a b c d)). Qed.
Lemma lem1308353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1308293 A x) (@lem1308292 A x)). Qed.
Lemma lem1308354 (x : nat) : (x = x) = True.
Proof. exact (@lem1308353 nat x). Qed.
Lemma lem1308355 (a : nat) (b : nat) (c : nat) (d : nat) : ((term21 a b c d) = (term21 a b c d)) = True.
Proof. exact (@lem1308354 (term21 a b c d)). Qed.
Lemma lem1308356 (a : nat) (c : nat) (b : nat) (d : nat) : ((term20 a b c d) = (term20 a c b d)) = True.
Proof. exact (TRANS (@lem1308351 a b c d) (@lem1308355 a b c d)). Qed.
Lemma lem1308357 (a : nat) (c : nat) (b : nat) (d : nat) : True = ((term20 a b c d) = (term20 a c b d)).
Proof. exact (SYM (@lem1308356 a c b d)). Qed.
Lemma lem1308359 (m : nat) : term24 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1308360 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1308361 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1308360 m) (@lem1308359 m)). Qed.
Lemma lem1308362 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1308361 m n). Qed.
Lemma lem1308363 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1308364 (m : nat) (n : nat) : term27 m n.
Proof. exact (EQ_MP (@lem1308363 m n) (@lem1308362 m n)). Qed.
Lemma lem1308365 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem1308364 m n p). Qed.
Lemma lem1308366 (m : nat) (n : nat) (p : nat) : (term28 m n p) = ((term29 m n p) = (term30 m n p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem1308368 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1308369 (m : nat) (h1 : term31) : term32 m.
Proof. exact (@lem1308368 h1 m). Qed.
Lemma lem1308370 (m : nat) : (term32 m) = (term33 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1308371 (m : nat) (h1 : term31) : term33 m.
Proof. exact (EQ_MP (@lem1308370 m) (@lem1308369 m h1)). Qed.
Lemma lem1308372 (m : nat) (n : nat) (h1 : term31) : term34 m n.
Proof. exact (@lem1308371 m h1 n). Qed.
Lemma lem1308373 (n : nat) (m : nat) : (term34 m n) = (term35 n m).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1308374 (n : nat) (m : nat) (h1 : term31) : term35 n m.
Proof. exact (EQ_MP (@lem1308373 n m) (@lem1308372 m n h1)). Qed.
Lemma lem1308375 (n : nat) (m : nat) (p : nat) (h1 : term31) : term36 n m p.
Proof. exact (@lem1308374 n m h1 p). Qed.
Lemma lem1308376 (n : nat) (m : nat) (p : nat) : (term36 n m p) = (term37 n m p).
Proof. exact (eq_refl (term36 n m p)). Qed.
Lemma lem1308377 (n : nat) (m : nat) (p : nat) (h1 : term31) : term37 n m p.
Proof. exact (EQ_MP (@lem1308376 n m p) (@lem1308375 n m p h1)). Qed.
Lemma lem1308378 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term31) : term38 n m p q.
Proof. exact (@lem1308377 n m p h1 q). Qed.
Lemma lem1308379 (n : nat) (m : nat) (p : nat) (q : nat) : (term38 n m p q) = (term39 n m p q).
Proof. exact (eq_refl (term38 n m p q)). Qed.
Lemma lem1308380 (n : nat) (m : nat) (p : nat) (q : nat) (h1 : term31) : term39 n m p q.
Proof. exact (EQ_MP (@lem1308379 n m p q) (@lem1308378 n m p q h1)). Qed.
Lemma lem1308381 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term40 m n p q) : term40 m n p q.
Proof. exact (h1). Qed.
Lemma lem1308382 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term31) (h2 : term40 m n p q) : term41 m p q.
Proof. exact (@lem1308380 n m p q h1 (@lem1308381 m n p q h2)). Qed.
Lemma lem1308383 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term40 m n p q) : term42 m p q.
Proof. exact (fun h0 : term31 => @lem1308382 m n p q h0 h1). Qed.
Lemma lem1308384 (m : nat) (p : nat) (q : nat) (h1 : term43 m p q) : term43 m p q.
Proof. exact (h1). Qed.
Lemma lem1308385 (m : nat) (p : nat) (q : nat) (h1 : term43 m p q) : term42 m p q.
Proof. exact (ex_elim (@lem1308384 m p q h1) (fun n : nat => fun h0 : term44 m p q n => @lem1308383 m n p q h0)). Qed.
Lemma lem1308386 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1308387 (m : nat) (p : nat) (q : nat) (h1 : term31) (h2 : term43 m p q) : term41 m p q.
Proof. exact (@lem1308385 m p q h2 (@lem1308386 h1)). Qed.
Lemma lem1308388 (m : nat) (p : nat) (q : nat) (h1 : term31) : term45 m p q.
Proof. exact (fun h0 : term43 m p q => @lem1308387 m p q h1 h0). Qed.
Lemma lem1308389 (m : nat) (p : nat) (h1 : term31) : term46 m p.
Proof. exact (fun q : nat => @lem1308388 m p q h1). Qed.
Lemma lem1308390 (m : nat) (h1 : term31) : term47 m.
Proof. exact (fun p : nat => @lem1308389 m p h1). Qed.
Lemma lem1308391 (h1 : term31) : term48.
Proof. exact (fun m : nat => @lem1308390 m h1). Qed.
Lemma lem1308392 : term49.
Proof. exact (fun h0 : term31 => @lem1308391 h0). Qed.
Lemma lem1308393 : term48.
Proof. exact (@lem1308392 (@lem1259806)). Qed.
Lemma lem1308394 (m : nat) : term50 m.
Proof. exact (@lem1308393 m). Qed.
Lemma lem1308395 (m : nat) : (term50 m) = (term47 m).
Proof. exact (eq_refl (term50 m)). Qed.
Lemma lem1308396 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1308395 m) (@lem1308394 m)). Qed.
Lemma lem1308397 (m : nat) (p : nat) : term51 m p.
Proof. exact (@lem1308396 m p). Qed.
Lemma lem1308398 (m : nat) (p : nat) : (term51 m p) = (term46 m p).
Proof. exact (eq_refl (term51 m p)). Qed.
Lemma lem1308399 (m : nat) (p : nat) : term46 m p.
Proof. exact (EQ_MP (@lem1308398 m p) (@lem1308397 m p)). Qed.
Lemma lem1308400 (m : nat) (p : nat) (q : nat) : term52 m p q.
Proof. exact (@lem1308399 m p q). Qed.
Lemma lem1308401 (m : nat) (p : nat) (q : nat) : (term52 m p q) = (term45 m p q).
Proof. exact (eq_refl (term52 m p q)). Qed.
Lemma lem1308403 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1308404 (m : nat) (h1 : term53) : term54 m.
Proof. exact (@lem1308403 h1 m). Qed.
Lemma lem1308405 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem1308406 (m : nat) (h1 : term53) : term55 m.
Proof. exact (EQ_MP (@lem1308405 m) (@lem1308404 m h1)). Qed.
Lemma lem1308407 (m : nat) (n : nat) (h1 : term53) : term56 m n.
Proof. exact (@lem1308406 m h1 n). Qed.
Lemma lem1308408 (n : nat) (m : nat) : (term56 m n) = (term57 n m).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem1308409 (n : nat) (m : nat) (h1 : term53) : term57 n m.
Proof. exact (EQ_MP (@lem1308408 n m) (@lem1308407 m n h1)). Qed.
Lemma lem1308410 (n : nat) (m : nat) (p : nat) (h1 : term53) : term58 n m p.
Proof. exact (@lem1308409 n m h1 p). Qed.
Lemma lem1308411 (n : nat) (m : nat) (p : nat) : (term58 n m p) = (term59 n m p).
Proof. exact (eq_refl (term58 n m p)). Qed.
Lemma lem1308412 (n : nat) (m : nat) (p : nat) (h1 : term53) : term59 n m p.
Proof. exact (EQ_MP (@lem1308411 n m p) (@lem1308410 n m p h1)). Qed.
Lemma lem1308413 (m : nat) (n : nat) (p : nat) (h1 : term60 m n p) : term60 m n p.
Proof. exact (h1). Qed.
Lemma lem1308414 (m : nat) (n : nat) (p : nat) (h1 : term53) (h2 : term60 m n p) : Peano.le m p.
Proof. exact (@lem1308412 n m p h1 (@lem1308413 m n p h2)). Qed.
Lemma lem1308415 (m : nat) (n : nat) (p : nat) (h1 : term60 m n p) : term61 m p.
Proof. exact (fun h0 : term53 => @lem1308414 m n p h0 h1). Qed.
Lemma lem1308416 (m : nat) (p : nat) (h1 : term62 m p) : term62 m p.
Proof. exact (h1). Qed.
Lemma lem1308417 (m : nat) (p : nat) (h1 : term62 m p) : term61 m p.
Proof. exact (ex_elim (@lem1308416 m p h1) (fun n : nat => fun h0 : term63 m p n => @lem1308415 m n p h0)). Qed.
Lemma lem1308418 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1308419 (m : nat) (p : nat) (h1 : term53) (h2 : term62 m p) : Peano.le m p.
Proof. exact (@lem1308417 m p h2 (@lem1308418 h1)). Qed.
Lemma lem1308420 (m : nat) (p : nat) (h1 : term53) : term64 m p.
Proof. exact (fun h0 : term62 m p => @lem1308419 m p h1 h0). Qed.
Lemma lem1308421 (m : nat) (h1 : term53) : term65 m.
Proof. exact (fun p : nat => @lem1308420 m p h1). Qed.
Lemma lem1308422 (h1 : term53) : term66.
Proof. exact (fun m : nat => @lem1308421 m h1). Qed.
Lemma lem1308423 : term67.
Proof. exact (fun h0 : term53 => @lem1308422 h0). Qed.
Lemma lem1308424 : term66.
Proof. exact (@lem1308423 (@lem93743)). Qed.
Lemma lem1308425 (m : nat) : term68 m.
Proof. exact (@lem1308424 m). Qed.
Lemma lem1308426 (m : nat) : (term68 m) = (term65 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem1308427 (m : nat) : term65 m.
Proof. exact (EQ_MP (@lem1308426 m) (@lem1308425 m)). Qed.
Lemma lem1308428 (m : nat) (p : nat) : term69 m p.
Proof. exact (@lem1308427 m p). Qed.
Lemma lem1308429 (m : nat) (p : nat) : (term69 m p) = (term64 m p).
Proof. exact (eq_refl (term69 m p)). Qed.
Lemma lem1308431 (P : nat -> nat) : term70 P.
Proof. exact (@lem1262185 P). Qed.
Lemma lem1308432 (P : nat -> nat) : (term70 P) = (term71 P).
Proof. exact (eq_refl (term70 P)). Qed.
Lemma lem1308433 (P : nat -> nat) : term71 P.
Proof. exact (EQ_MP (@lem1308432 P) (@lem1308431 P)). Qed.
Lemma lem1308434 (P : nat -> nat) (Q : nat -> nat) : term72 P Q.
Proof. exact (@lem1308433 P Q). Qed.
Lemma lem1308435 (P : nat -> nat) (Q : nat -> nat) : (term72 P Q) = ((term73 P Q) = (term74 P Q)).
Proof. exact (eq_refl (term72 P Q)). Qed.
Lemma lem1308437 (x : nadd) : term75 x.
Proof. exact (@lem1263160 x). Qed.
Lemma lem1308438 (x : nadd) : (term75 x) = (term76 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1308439 (x : nadd) : term76 x.
Proof. exact (EQ_MP (@lem1308438 x) (@lem1308437 x)). Qed.
Lemma lem1308440 (x : nadd) (A' : nat) (h1 : term77 x A') : term77 x A'.
Proof. exact (h1). Qed.
Lemma lem1308441 (x : nadd) : term78 x.
Proof. exact (@lem1302159 x). Qed.
Lemma lem1308442 (x : nadd) : (term78 x) = (term79 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1308444 : term80.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1308445 : term81.
Proof. exact (proj2 (@lem1308444)). Qed.
Lemma lem1308466 : term82.
Proof. exact (proj1 (@lem1308445)). Qed.
Lemma lem1308467 (n : nat) : term83 n.
Proof. exact (@lem1308466 n). Qed.
Lemma lem1308468 (n : nat) : (term83 n) = ((term84 n) = n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem1308478 (k : nat) : term85 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1308479 (k : nat) : (term85 k) = ((term86 k) = (term87 k)).
Proof. exact (eq_refl (term85 k)). Qed.
Lemma lem1308481 (m : nat) : term88 m.
Proof. exact (@lem1245388 m). Qed.
Lemma lem1308482 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1308483 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem1308482 m) (@lem1308481 m)). Qed.
Lemma lem1308484 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1308483 m n). Qed.
Lemma lem1308485 (n : nat) (m : nat) : (term90 m n) = (term91 n m).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1308486 (n : nat) (m : nat) : term91 n m.
Proof. exact (EQ_MP (@lem1308485 n m) (@lem1308484 m n)). Qed.
Lemma lem1308487 (n : nat) (m : nat) (p : nat) : term92 n m p.
Proof. exact (@lem1308486 n m p). Qed.
Lemma lem1308488 (n : nat) (m : nat) (p : nat) : (term92 n m p) = ((term93 m n p) = (term94 n m p)).
Proof. exact (eq_refl (term92 n m p)). Qed.
Lemma lem1308490 (x : nadd) : term95 x.
Proof. exact (@lem1267473 (nadd_inv x)). Qed.
Lemma lem1308491 (x : nadd) : (term95 x) = (term96 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1308492 (x : nadd) : term96 x.
Proof. exact (EQ_MP (@lem1308491 x) (@lem1308490 x)). Qed.
Lemma lem1308493 (x : nadd) : term97 x.
Proof. exact (@lem1308492 x x). Qed.
Lemma lem1308494 (x : nadd) : (term97 x) = (term98 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1308495 (x : nadd) : term98 x.
Proof. exact (EQ_MP (@lem1308494 x) (@lem1308493 x)). Qed.
Lemma lem1308496 (x : nadd) (A1 : nat) (h1 : term99 x A1) : term99 x A1.
Proof. exact (h1). Qed.
Lemma lem1308497 (P : nat -> nat) : term100 P.
Proof. exact (@lem1261317 P). Qed.
Lemma lem1308498 (P : nat -> nat) : (term100 P) = ((term101 P) = (term102 P)).
Proof. exact (eq_refl (term100 P)). Qed.
Lemma lem1308500 (x : nadd) : term103 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1308501 (x : nadd) : (term103 x) = (term104 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1308502 (x : nadd) : term104 x.
Proof. exact (EQ_MP (@lem1308501 x) (@lem1308500 x)). Qed.
Lemma lem1308503 (x : nadd) (y : nadd) : term105 x y.
Proof. exact (@lem1308502 x y). Qed.
Lemma lem1308504 (x : nadd) (y : nadd) : (term105 x y) = ((term106 x y) = (term107 x y)).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1308506 (x : nadd) : term108 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1308507 (x : nadd) : (term108 x) = (term109 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1308508 (x : nadd) : term109 x.
Proof. exact (EQ_MP (@lem1308507 x) (@lem1308506 x)). Qed.
Lemma lem1308509 (x : nadd) (y : nadd) : term110 x y.
Proof. exact (@lem1308508 x y). Qed.
Lemma lem1308510 (x : nadd) (y : nadd) : (term110 x y) = ((nadd_eq x y) = (term111 x y)).
Proof. exact (eq_refl (term110 x y)). Qed.
Lemma lem1308512 (x : nadd) (h1 : term112 x) : term112 x.
Proof. exact (h1). Qed.
Lemma lem1308514 (x : nadd) (y : nadd) : (nadd_eq x y) = (term111 x y).
Proof. exact (EQ_MP (@lem1308510 x y) (@lem1308509 x y)). Qed.
Lemma lem1308515 (x : nadd) : (term113 x) = (term114 x).
Proof. exact (@lem1308514 (term115 x) term116). Qed.
Lemma lem1308525 (x : nadd) (y : nadd) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem1308504 x y) (@lem1308503 x y)). Qed.
Lemma lem1308526 (x : nadd) : (term117 x) = (term118 x).
Proof. exact (@lem1308525 (nadd_inv x) x). Qed.
Lemma lem1308527 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1308528 (x : nadd) (n : nat) : (term119 x n) = (term120 x n).
Proof. exact (MK_COMB (@lem1308526 x) (@lem1308527 n)). Qed.
Lemma lem1308530 {A B : Type'} (f : A -> B) (y : A) : (term121 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1308531 (f : nat -> nat) (y : nat) : (term122 f y) = (f y).
Proof. exact (@lem1308530 nat nat f y). Qed.
Lemma lem1308532 (x : nadd) (n : nat) : (term123 x n) = (term120 x n).
Proof. exact (@lem1308531 (term118 x) n). Qed.
Lemma lem1308533 (x : nadd) (n : nat) : (term120 x n) = (term124 x n).
Proof. exact (eq_refl (term120 x n)). Qed.
Lemma lem1308534 (x : nadd) : (term125 x) = (term118 x).
Proof. exact (fun_ext (fun n : nat => @lem1308533 x n)). Qed.
Lemma lem1308535 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1308536 (x : nadd) (n : nat) : (term123 x n) = (term120 x n).
Proof. exact (MK_COMB (@lem1308534 x) (@lem1308535 n)). Qed.
Lemma lem1308537 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1308538 (x : nadd) (n : nat) : (term126 x n) = (term127 x n).
Proof. exact (MK_COMB (@lem1308537) (@lem1308536 x n)). Qed.
Lemma lem1308539 (x : nadd) (n : nat) : (term120 x n) = (term124 x n).
Proof. exact (eq_refl (term120 x n)). Qed.
Lemma lem1308540 (x : nadd) (n : nat) : ((term123 x n) = (term120 x n)) = ((term120 x n) = (term124 x n)).
Proof. exact (MK_COMB (@lem1308538 x n) (@lem1308539 x n)). Qed.
Lemma lem1308541 (x : nadd) (n : nat) : (term120 x n) = (term124 x n).
Proof. exact (EQ_MP (@lem1308540 x n) (@lem1308532 x n)). Qed.
Lemma lem1308542 (x : nadd) (n : nat) : (term119 x n) = (term124 x n).
Proof. exact (TRANS (@lem1308528 x n) (@lem1308541 x n)). Qed.
Lemma lem1308543 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1308544 (x : nadd) (n : nat) : (term128 x n) = (term129 x n).
Proof. exact (MK_COMB (@lem1308543) (@lem1308542 x n)). Qed.
Lemma lem1308545 (n : nat) : (term130 n) = (term130 n).
Proof. exact (eq_refl (term130 n)). Qed.
Lemma lem1308546 (x : nadd) (n : nat) : (term131 x n) = (term132 x n).
Proof. exact (MK_COMB (@lem1308544 x n) (@lem1308545 n)). Qed.
Lemma lem1308547 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1308548 (x : nadd) (n : nat) : (term133 x n) = (term134 x n).
Proof. exact (MK_COMB (@lem1308547) (@lem1308546 x n)). Qed.
Lemma lem1308549 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308550 (x : nadd) (n : nat) : (term135 x n) = (term136 x n).
Proof. exact (MK_COMB (@lem1308549) (@lem1308548 x n)). Qed.
Lemma lem1308551 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1308552 (x : nadd) (n : nat) (B : nat) : (term137 x n B) = (term138 x n B).
Proof. exact (MK_COMB (@lem1308550 x n) (@lem1308551 B)). Qed.
Lemma lem1308553 (x : nadd) (B : nat) : (term139 x B) = (term140 x B).
Proof. exact (fun_ext (fun n : nat => @lem1308552 x n B)). Qed.
Lemma lem1308554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308555 (x : nadd) (B : nat) : (term141 x B) = (term142 x B).
Proof. exact (MK_COMB (@lem1308554) (@lem1308553 x B)). Qed.
Lemma lem1308560 (x : nadd) : (term143 x) = (term144 x).
Proof. exact (fun_ext (fun B : nat => @lem1308555 x B)). Qed.
Lemma lem1308561 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308562 (x : nadd) : (term114 x) = (term145 x).
Proof. exact (MK_COMB (@lem1308561) (@lem1308560 x)). Qed.
Lemma lem1308567 (x : nadd) : (term113 x) = (term145 x).
Proof. exact (TRANS (@lem1308515 x) (@lem1308562 x)). Qed.
Lemma lem1308568 (x : nadd) : (term145 x) = (term113 x).
Proof. exact (SYM (@lem1308567 x)). Qed.
Lemma lem1308570 (P : nat -> nat) : (term101 P) = (term102 P).
Proof. exact (EQ_MP (@lem1308498 P) (@lem1308497 P)). Qed.
Lemma lem1308571 (x : nadd) : (term146 x) = (term147 x).
Proof. exact (@lem1308570 (term148 x)). Qed.
Lemma lem1308572 (x : nadd) (n : nat) : (term149 x n) = (term134 x n).
Proof. exact (eq_refl (term149 x n)). Qed.
Lemma lem1308573 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308574 (x : nadd) (n : nat) : (term150 x n) = (term136 x n).
Proof. exact (MK_COMB (@lem1308573) (@lem1308572 x n)). Qed.
Lemma lem1308575 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1308576 (x : nadd) (n : nat) (B : nat) : (term151 x n B) = (term138 x n B).
Proof. exact (MK_COMB (@lem1308574 x n) (@lem1308575 B)). Qed.
Lemma lem1308577 (x : nadd) (B : nat) : (term152 x B) = (term140 x B).
Proof. exact (fun_ext (fun n : nat => @lem1308576 x n B)). Qed.
Lemma lem1308578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308579 (x : nadd) (B : nat) : (term153 x B) = (term142 x B).
Proof. exact (MK_COMB (@lem1308578) (@lem1308577 x B)). Qed.
Lemma lem1308580 (x : nadd) : (term154 x) = (term144 x).
Proof. exact (fun_ext (fun B : nat => @lem1308579 x B)). Qed.
Lemma lem1308581 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308582 (x : nadd) : (term146 x) = (term145 x).
Proof. exact (MK_COMB (@lem1308581) (@lem1308580 x)). Qed.
Lemma lem1308583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1308584 (x : nadd) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1308583) (@lem1308582 x)). Qed.
Lemma lem1308585 (x : nadd) (n : nat) : (term149 x n) = (term134 x n).
Proof. exact (eq_refl (term149 x n)). Qed.
Lemma lem1308586 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1308587 (x : nadd) (n : nat) : (term157 x n) = (term158 x n).
Proof. exact (MK_COMB (@lem1308586 n) (@lem1308585 x n)). Qed.
Lemma lem1308588 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308589 (x : nadd) (n : nat) : (term159 x n) = (term160 x n).
Proof. exact (MK_COMB (@lem1308588) (@lem1308587 x n)). Qed.
Lemma lem1308590 (A : nat) (n : nat) (B : nat) : (term161 A n B) = (term161 A n B).
Proof. exact (eq_refl (term161 A n B)). Qed.
Lemma lem1308591 (x : nadd) (A : nat) (n : nat) (B : nat) : (term162 x A n B) = (term163 x A n B).
Proof. exact (MK_COMB (@lem1308589 x n) (@lem1308590 A n B)). Qed.
Lemma lem1308592 (x : nadd) (A : nat) (B : nat) : (term164 x A B) = (term165 x A B).
Proof. exact (fun_ext (fun n : nat => @lem1308591 x A n B)). Qed.
Lemma lem1308593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308594 (x : nadd) (A : nat) (B : nat) : (term166 x A B) = (term167 x A B).
Proof. exact (MK_COMB (@lem1308593) (@lem1308592 x A B)). Qed.
Lemma lem1308595 (x : nadd) (A : nat) : (term168 x A) = (term169 x A).
Proof. exact (fun_ext (fun B : nat => @lem1308594 x A B)). Qed.
Lemma lem1308596 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308597 (x : nadd) (A : nat) : (term170 x A) = (term171 x A).
Proof. exact (MK_COMB (@lem1308596) (@lem1308595 x A)). Qed.
Lemma lem1308598 (x : nadd) : (term172 x) = (term173 x).
Proof. exact (fun_ext (fun A : nat => @lem1308597 x A)). Qed.
Lemma lem1308599 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308600 (x : nadd) : (term147 x) = (term174 x).
Proof. exact (MK_COMB (@lem1308599) (@lem1308598 x)). Qed.
Lemma lem1308601 (x : nadd) : ((term146 x) = (term147 x)) = ((term145 x) = (term174 x)).
Proof. exact (MK_COMB (@lem1308584 x) (@lem1308600 x)). Qed.
Lemma lem1308602 (x : nadd) : (term145 x) = (term174 x).
Proof. exact (EQ_MP (@lem1308601 x) (@lem1308571 x)). Qed.
Lemma lem1308603 (x : nadd) : (term174 x) = (term145 x).
Proof. exact (SYM (@lem1308602 x)). Qed.
Lemma lem1308604 (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : term175 x A1 B1.
Proof. exact (h1). Qed.
Lemma lem1308618 (n : nat) (m : nat) (p : nat) : (term93 m n p) = (term94 n m p).
Proof. exact (EQ_MP (@lem1308488 n m p) (@lem1308487 n m p)). Qed.
Lemma lem1308619 (x : nadd) (n : nat) : (term158 x n) = (term176 x n).
Proof. exact (@lem1308618 (term124 x n) n (term130 n)). Qed.
Lemma lem1308621 (k : nat) : (term86 k) = (term87 k).
Proof. exact (EQ_MP (@lem1308479 k) (@lem1308478 k)). Qed.
Lemma lem1308622 : term177 = term178.
Proof. exact (@lem1308621 term179). Qed.
Lemma lem1308624 (n : nat) : (term84 n) = n.
Proof. exact (EQ_MP (@lem1308468 n) (@lem1308467 n)). Qed.
Lemma lem1308625 : term178 = term180.
Proof. exact (fun_ext (fun n : nat => @lem1308624 n)). Qed.
Lemma lem1308626 : term177 = term180.
Proof. exact (TRANS (@lem1308622) (@lem1308625)). Qed.
Lemma lem1308627 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1308628 (n : nat) : (term130 n) = (term181 n).
Proof. exact (MK_COMB (@lem1308626) (@lem1308627 n)). Qed.
Lemma lem1308630 {A B : Type'} (f : A -> B) (y : A) : (term121 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1308631 (f : nat -> nat) (y : nat) : (term122 f y) = (f y).
Proof. exact (@lem1308630 nat nat f y). Qed.
Lemma lem1308632 (n : nat) : (term182 n) = (term181 n).
Proof. exact (@lem1308631 term180 n). Qed.
Lemma lem1308633 (n : nat) : (term181 n) = n.
Proof. exact (eq_refl (term181 n)). Qed.
Lemma lem1308634 : term183 = term180.
Proof. exact (fun_ext (fun n : nat => @lem1308633 n)). Qed.
Lemma lem1308635 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1308636 (n : nat) : (term182 n) = (term181 n).
Proof. exact (MK_COMB (@lem1308634) (@lem1308635 n)). Qed.
Lemma lem1308637 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1308638 (n : nat) : (term184 n) = (term185 n).
Proof. exact (MK_COMB (@lem1308637) (@lem1308636 n)). Qed.
Lemma lem1308639 (n : nat) : (term181 n) = n.
Proof. exact (eq_refl (term181 n)). Qed.
Lemma lem1308640 (n : nat) : ((term182 n) = (term181 n)) = ((term181 n) = n).
Proof. exact (MK_COMB (@lem1308638 n) (@lem1308639 n)). Qed.
Lemma lem1308641 (n : nat) : (term181 n) = n.
Proof. exact (EQ_MP (@lem1308640 n) (@lem1308632 n)). Qed.
Lemma lem1308642 (n : nat) : (term130 n) = n.
Proof. exact (TRANS (@lem1308628 n) (@lem1308641 n)). Qed.
Lemma lem1308643 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1308644 (n : nat) : (term186 n) = (Nat.mul n n).
Proof. exact (MK_COMB (@lem1308643 n) (@lem1308642 n)). Qed.
Lemma lem1308645 (x : nadd) (n : nat) : (term187 x n) = (term187 x n).
Proof. exact (eq_refl (term187 x n)). Qed.
Lemma lem1308646 (x : nadd) (n : nat) : (term188 x n) = (term189 x n).
Proof. exact (MK_COMB (@lem1308645 x n) (@lem1308644 n)). Qed.
Lemma lem1308647 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1308648 (x : nadd) (n : nat) : (term176 x n) = (term190 x n).
Proof. exact (MK_COMB (@lem1308647) (@lem1308646 x n)). Qed.
Lemma lem1308649 (x : nadd) (n : nat) : (term158 x n) = (term190 x n).
Proof. exact (TRANS (@lem1308619 x n) (@lem1308648 x n)). Qed.
Lemma lem1308650 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308651 (x : nadd) (n : nat) : (term160 x n) = (term191 x n).
Proof. exact (MK_COMB (@lem1308650) (@lem1308649 x n)). Qed.
Lemma lem1308652 (A : nat) (n : nat) (B : nat) : (term161 A n B) = (term161 A n B).
Proof. exact (eq_refl (term161 A n B)). Qed.
Lemma lem1308653 (x : nadd) (A : nat) (n : nat) (B : nat) : (term163 x A n B) = (term192 x A n B).
Proof. exact (MK_COMB (@lem1308651 x n) (@lem1308652 A n B)). Qed.
Lemma lem1308654 (x : nadd) (A : nat) (B : nat) : (term165 x A B) = (term193 x A B).
Proof. exact (fun_ext (fun n : nat => @lem1308653 x A n B)). Qed.
Lemma lem1308655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308656 (x : nadd) (A : nat) (B : nat) : (term167 x A B) = (term194 x A B).
Proof. exact (MK_COMB (@lem1308655) (@lem1308654 x A B)). Qed.
Lemma lem1308661 (x : nadd) (A : nat) : (term169 x A) = (term195 x A).
Proof. exact (fun_ext (fun B : nat => @lem1308656 x A B)). Qed.
Lemma lem1308662 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308663 (x : nadd) (A : nat) : (term171 x A) = (term196 x A).
Proof. exact (MK_COMB (@lem1308662) (@lem1308661 x A)). Qed.
Lemma lem1308668 (x : nadd) : (term173 x) = (term197 x).
Proof. exact (fun_ext (fun A : nat => @lem1308663 x A)). Qed.
Lemma lem1308669 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308670 (x : nadd) : (term174 x) = (term198 x).
Proof. exact (MK_COMB (@lem1308669) (@lem1308668 x)). Qed.
Lemma lem1308675 (x : nadd) : (term198 x) = (term174 x).
Proof. exact (SYM (@lem1308670 x)). Qed.
Lemma lem1308679 (x : nadd) : term79 x.
Proof. exact (EQ_MP (@lem1308442 x) (@lem1308441 x)). Qed.
Lemma lem1308680 (x : nadd) (h1 : term112 x) : term199 x.
Proof. exact (@lem1308679 x (@lem1308512 x h1)). Qed.
Lemma lem1308681 (N : nat) (x : nadd) (h1 : term200 N x) : term200 N x.
Proof. exact (h1). Qed.
Lemma lem1308682 (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : term201 x A' B'.
Proof. exact (h1). Qed.
Lemma lem1308683 (x : nadd) (h1 : term202 x) : term202 x.
Proof. exact (h1). Qed.
Lemma lem1308684 (x : nadd) (A2 : nat) (h1 : term203 x A2) : term203 x A2.
Proof. exact (h1). Qed.
Lemma lem1308685 (x : nadd) (A2 : nat) (B2 : nat) (h1 : term204 x A2 B2) : term204 x A2 B2.
Proof. exact (h1). Qed.
Lemma lem1308687 (P : nat -> nat) (Q : nat -> nat) : (term73 P Q) = (term74 P Q).
Proof. exact (EQ_MP (@lem1308435 P Q) (@lem1308434 P Q)). Qed.
Lemma lem1308688 (x : nadd) (A' : nat) : (term205 x A') = (term206 x A').
Proof. exact (@lem1308687 (term207 x) (term87 A')). Qed.
Lemma lem1308689 (x : nadd) (n : nat) : (term208 x n) = (term209 x n).
Proof. exact (eq_refl (term208 x n)). Qed.
Lemma lem1308690 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308691 (x : nadd) (n : nat) : (term210 x n) = (term211 x n).
Proof. exact (MK_COMB (@lem1308690) (@lem1308689 x n)). Qed.
Lemma lem1308692 (A' : nat) (n : nat) : (term212 A' n) = (Nat.mul A' n).
Proof. exact (eq_refl (term212 A' n)). Qed.
Lemma lem1308693 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1308694 (A' : nat) (n : nat) : (term213 A' n) = (term214 A' n).
Proof. exact (MK_COMB (@lem1308693) (@lem1308692 A' n)). Qed.
Lemma lem1308695 (B2 : nat) : B2 = B2.
Proof. exact (eq_refl B2). Qed.
Lemma lem1308696 (A' : nat) (n : nat) (B2 : nat) : (term215 A' n B2) = (term161 A' n B2).
Proof. exact (MK_COMB (@lem1308694 A' n) (@lem1308695 B2)). Qed.
Lemma lem1308697 (x : nadd) (A' : nat) (n : nat) (B2 : nat) : (term216 x A' n B2) = (term217 x A' n B2).
Proof. exact (MK_COMB (@lem1308691 x n) (@lem1308696 A' n B2)). Qed.
Lemma lem1308698 (x : nadd) (A' : nat) (B2 : nat) : (term218 x A' B2) = (term219 x A' B2).
Proof. exact (fun_ext (fun n : nat => @lem1308697 x A' n B2)). Qed.
Lemma lem1308699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308700 (x : nadd) (A' : nat) (B2 : nat) : (term220 x A' B2) = (term204 x A' B2).
Proof. exact (MK_COMB (@lem1308699) (@lem1308698 x A' B2)). Qed.
Lemma lem1308701 (x : nadd) (A' : nat) : (term221 x A') = (term222 x A').
Proof. exact (fun_ext (fun B2 : nat => @lem1308700 x A' B2)). Qed.
Lemma lem1308702 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308703 (x : nadd) (A' : nat) : (term205 x A') = (term203 x A').
Proof. exact (MK_COMB (@lem1308702) (@lem1308701 x A')). Qed.
Lemma lem1308704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1308705 (x : nadd) (A' : nat) : (term223 x A') = (term224 x A').
Proof. exact (MK_COMB (@lem1308704) (@lem1308703 x A')). Qed.
Lemma lem1308706 (x : nadd) (n : nat) : (term208 x n) = (term209 x n).
Proof. exact (eq_refl (term208 x n)). Qed.
Lemma lem1308707 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308708 (x : nadd) (n : nat) : (term210 x n) = (term211 x n).
Proof. exact (MK_COMB (@lem1308707) (@lem1308706 x n)). Qed.
Lemma lem1308709 (A' : nat) (n : nat) : (term212 A' n) = (Nat.mul A' n).
Proof. exact (eq_refl (term212 A' n)). Qed.
Lemma lem1308710 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1308711 (A' : nat) (n : nat) : (term213 A' n) = (term214 A' n).
Proof. exact (MK_COMB (@lem1308710) (@lem1308709 A' n)). Qed.
Lemma lem1308712 (B2 : nat) : B2 = B2.
Proof. exact (eq_refl B2). Qed.
Lemma lem1308713 (A' : nat) (n : nat) (B2 : nat) : (term215 A' n B2) = (term161 A' n B2).
Proof. exact (MK_COMB (@lem1308711 A' n) (@lem1308712 B2)). Qed.
Lemma lem1308714 (x : nadd) (A' : nat) (n : nat) (B2 : nat) : (term216 x A' n B2) = (term217 x A' n B2).
Proof. exact (MK_COMB (@lem1308708 x n) (@lem1308713 A' n B2)). Qed.
Lemma lem1308715 (N : nat) (n : nat) : (term225 N n) = (term225 N n).
Proof. exact (eq_refl (term225 N n)). Qed.
Lemma lem1308716 (N : nat) (x : nadd) (A' : nat) (n : nat) (B2 : nat) : (term226 N x A' n B2) = (term227 N x A' n B2).
Proof. exact (MK_COMB (@lem1308715 N n) (@lem1308714 x A' n B2)). Qed.
Lemma lem1308717 (N : nat) (x : nadd) (A' : nat) (B2 : nat) : (term228 N x A' B2) = (term229 N x A' B2).
Proof. exact (fun_ext (fun n : nat => @lem1308716 N x A' n B2)). Qed.
Lemma lem1308718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1308719 (N : nat) (x : nadd) (A' : nat) (B2 : nat) : (term230 N x A' B2) = (term231 N x A' B2).
Proof. exact (MK_COMB (@lem1308718) (@lem1308717 N x A' B2)). Qed.
Lemma lem1308720 (x : nadd) (A' : nat) (B2 : nat) : (term232 x A' B2) = (term233 x A' B2).
Proof. exact (fun_ext (fun N : nat => @lem1308719 N x A' B2)). Qed.
Lemma lem1308721 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308722 (x : nadd) (A' : nat) (B2 : nat) : (term234 x A' B2) = (term235 x A' B2).
Proof. exact (MK_COMB (@lem1308721) (@lem1308720 x A' B2)). Qed.
Lemma lem1308723 (x : nadd) (A' : nat) : (term236 x A') = (term237 x A').
Proof. exact (fun_ext (fun B2 : nat => @lem1308722 x A' B2)). Qed.
Lemma lem1308724 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1308725 (x : nadd) (A' : nat) : (term206 x A') = (term238 x A').
Proof. exact (MK_COMB (@lem1308724) (@lem1308723 x A')). Qed.
Lemma lem1308726 (x : nadd) (A' : nat) : ((term205 x A') = (term206 x A')) = ((term203 x A') = (term238 x A')).
Proof. exact (MK_COMB (@lem1308705 x A') (@lem1308725 x A')). Qed.
Lemma lem1308727 (x : nadd) (A' : nat) : (term203 x A') = (term238 x A').
Proof. exact (EQ_MP (@lem1308726 x A') (@lem1308688 x A')). Qed.
Lemma lem1308728 (x : nadd) (A' : nat) : (term238 x A') = (term203 x A').
Proof. exact (SYM (@lem1308727 x A')). Qed.
Lemma lem1308729 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1308731 (m : nat) (p : nat) : term64 m p.
Proof. exact (EQ_MP (@lem1308429 m p) (@lem1308428 m p)). Qed.
Lemma lem1308732 (x : nadd) (A' : nat) (n : nat) (B' : nat) : term239 x A' n B'.
Proof. exact (@lem1308731 (term209 x n) (term161 A' n B')). Qed.
Lemma lem1308745 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : term240 x A' B' n.
Proof. exact (@lem1308682 x A' B' h1 n). Qed.
Lemma lem1308746 (x : nadd) (A' : nat) (n : nat) (B' : nat) : (term240 x A' B' n) = (term241 x A' n B').
Proof. exact (eq_refl (term240 x A' B' n)). Qed.
Lemma lem1308747 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : term241 x A' n B'.
Proof. exact (EQ_MP (@lem1308746 x A' n B') (@lem1308745 n x A' B' h1)). Qed.
Lemma lem1308748 (x : nadd) (A' : nat) (n : nat) (B' : nat) : (term241 x A' n B') = ((term241 x A' n B') = True).
Proof. exact (@lem7 (term241 x A' n B')). Qed.
Lemma lem1308755 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : (term241 x A' n B') = True.
Proof. exact (EQ_MP (@lem1308748 x A' n B') (@lem1308747 n x A' B' h1)). Qed.
Lemma lem1308756 (x : nadd) (n : nat) : (term242 x n) = (term242 x n).
Proof. exact (eq_refl (term242 x n)). Qed.
Lemma lem1308757 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : (term243 x A' n B') = (term244 x n).
Proof. exact (MK_COMB (@lem1308756 x n) (@lem1308755 n x A' B' h1)). Qed.
Lemma lem1308759 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1308760 (x : nadd) (n : nat) : (term244 x n) = (term245 x n).
Proof. exact (@lem1308759 (term245 x n)). Qed.
Lemma lem1308761 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : (term243 x A' n B') = (term245 x n).
Proof. exact (TRANS (@lem1308757 n x A' B' h1) (@lem1308760 x n)). Qed.
Lemma lem1308762 (n : nat) (x : nadd) (A' : nat) (B' : nat) (h1 : term201 x A' B') : (term245 x n) = (term243 x A' n B').
Proof. exact (SYM (@lem1308761 n x A' B' h1)). Qed.
Lemma lem1308763 (N : nat) (x : nadd) (h1 : term200 N x) : term200 N x.
Proof. exact (h1). Qed.
Lemma lem1308764 (n : nat) (N : nat) (x : nadd) (h1 : term200 N x) : term246 N x n.
Proof. exact (@lem1308763 N x h1 n). Qed.
Lemma lem1308765 (N : nat) (x : nadd) (n : nat) : (term246 N x n) = (term247 N x n).
Proof. exact (eq_refl (term246 N x n)). Qed.
Lemma lem1308766 (n : nat) (N : nat) (x : nadd) (h1 : term200 N x) : term247 N x n.
Proof. exact (EQ_MP (@lem1308765 N x n) (@lem1308764 n N x h1)). Qed.
Lemma lem1308767 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1308768 (x : nadd) (N : nat) (n : nat) (h1 : term200 N x) (h2 : Peano.le N n) : term245 x n.
Proof. exact (@lem1308766 n N x h1 (@lem1308767 N n h2)). Qed.
Lemma lem1308769 (x : nadd) (N : nat) (n : nat) (h1 : Peano.le N n) : term248 N x n.
Proof. exact (fun h0 : term200 N x => @lem1308768 x N n h0 h1). Qed.
Lemma lem1308770 (N : nat) (x : nadd) (h1 : term200 N x) : term200 N x.
Proof. exact (h1). Qed.
Lemma lem1308771 (x : nadd) (N : nat) (n : nat) (h1 : term200 N x) (h2 : Peano.le N n) : term245 x n.
Proof. exact (@lem1308769 x N n h2 (@lem1308770 N x h1)). Qed.
Lemma lem1308772 (n : nat) (N : nat) (x : nadd) (h1 : term200 N x) : term247 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1308771 x N n h1 h0). Qed.
Lemma lem1308773 (N : nat) (x : nadd) (h1 : term200 N x) : term200 N x.
Proof. exact (fun n : nat => @lem1308772 n N x h1). Qed.
Lemma lem1308774 (N : nat) (x : nadd) : term249 N x.
Proof. exact (fun h0 : term200 N x => @lem1308773 N x h0). Qed.
Lemma lem1308775 (N : nat) (x : nadd) (h1 : term200 N x) : term200 N x.
Proof. exact (@lem1308774 N x (@lem1308681 N x h1)). Qed.
Lemma lem1308776 (n : nat) (N : nat) (x : nadd) (h1 : term200 N x) : term246 N x n.
Proof. exact (@lem1308775 N x h1 n). Qed.
Lemma lem1308777 (N : nat) (x : nadd) (n : nat) : (term246 N x n) = (term247 N x n).
Proof. exact (eq_refl (term246 N x n)). Qed.
Lemma lem1308780 (n : nat) (N : nat) (x : nadd) (h1 : term200 N x) : term247 N x n.
Proof. exact (EQ_MP (@lem1308777 N x n) (@lem1308776 n N x h1)). Qed.
Lemma lem1308798 (N : nat) (n : nat) : (Peano.le N n) = ((Peano.le N n) = True).
Proof. exact (@lem7 (Peano.le N n)). Qed.
Lemma lem1308801 (N : nat) (n : nat) (h1 : Peano.le N n) : (Peano.le N n) = True.
Proof. exact (EQ_MP (@lem1308798 N n) (@lem1308729 N n h1)). Qed.
Lemma lem1308802 (N : nat) (n : nat) (h1 : Peano.le N n) : True = (Peano.le N n).
Proof. exact (SYM (@lem1308801 N n h1)). Qed.
Lemma lem1308803 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (EQ_MP (@lem1308802 N n h1) (@lem0)). Qed.
Lemma lem1308804 (x : nadd) (N : nat) (n : nat) (h1 : term200 N x) (h2 : Peano.le N n) : term245 x n.
Proof. exact (@lem1308780 n N x h1 (@lem1308803 N n h2)). Qed.
Lemma lem1308805 (A' : nat) (B' : nat) (x : nadd) (N : nat) (n : nat) (h1 : term201 x A' B') (h2 : term200 N x) (h3 : Peano.le N n) : term243 x A' n B'.
Proof. exact (EQ_MP (@lem1308762 n x A' B' h1) (@lem1308804 x N n h2 h3)). Qed.
Lemma lem1308806 (A' : nat) (B' : nat) (x : nadd) (N : nat) (n : nat) (h1 : term201 x A' B') (h2 : term200 N x) (h3 : Peano.le N n) : term250 x A' n B'.
Proof. exact (ex_intro (term251 x A' n B') (dest_nadd x n) (@lem1308805 A' B' x N n h1 h2 h3)). Qed.
Lemma lem1308807 (A' : nat) (B' : nat) (x : nadd) (N : nat) (n : nat) (h1 : term201 x A' B') (h2 : term200 N x) (h3 : Peano.le N n) : term217 x A' n B'.
Proof. exact (@lem1308732 x A' n B' (@lem1308806 A' B' x N n h1 h2 h3)). Qed.
Lemma lem1308808 (A' : nat) (B' : nat) (x : nadd) (N : nat) (n : nat) (h1 : term201 x A' B') (h2 : term200 N x) (h3 : Peano.le N n) : (Peano.le N n) = (term217 x A' n B').
Proof. exact (prop_ext (fun h4 : Peano.le N n => @lem1308807 A' B' x N n h1 h2 h3) (fun h4 : term217 x A' n B' => @lem1308729 N n h3)). Qed.
Lemma lem1308809 (A' : nat) (B' : nat) (x : nadd) (N : nat) (n : nat) (h1 : term201 x A' B') (h2 : term200 N x) (h3 : Peano.le N n) : term217 x A' n B'.
Proof. exact (EQ_MP (@lem1308808 A' B' x N n h1 h2 h3) (@lem1308729 N n h3)). Qed.
Lemma lem1308810 (n : nat) (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term227 N x A' n B'.
Proof. exact (fun h0 : Peano.le N n => @lem1308809 A' B' x N n h1 h2 h0). Qed.
Lemma lem1308815 (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term231 N x A' B'.
Proof. exact (fun n : nat => @lem1308810 n A' B' N x h1 h2). Qed.
Lemma lem1308816 (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term235 x A' B'.
Proof. exact (ex_intro (term233 x A' B') N (@lem1308815 A' B' N x h1 h2)). Qed.
Lemma lem1308817 (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term238 x A'.
Proof. exact (ex_intro (term237 x A') B' (@lem1308816 A' B' N x h1 h2)). Qed.
Lemma lem1308818 (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term203 x A'.
Proof. exact (EQ_MP (@lem1308728 x A') (@lem1308817 A' B' N x h1 h2)). Qed.
Lemma lem1308819 (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term201 x A' B') (h2 : term200 N x) : term202 x.
Proof. exact (ex_intro (term252 x) A' (@lem1308818 A' B' N x h1 h2)). Qed.
Lemma lem1308821 (m : nat) (p : nat) (q : nat) : term45 m p q.
Proof. exact (EQ_MP (@lem1308401 m p q) (@lem1308400 m p q)). Qed.
Lemma lem1308822 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : term253 x A1 A2 n B1 B2.
Proof. exact (@lem1308821 (term254 x n) (Nat.mul n n) (term255 A1 A2 n B1 B2)). Qed.
Lemma lem1308824 (m : nat) (n : nat) (p : nat) : (term29 m n p) = (term30 m n p).
Proof. exact (EQ_MP (@lem1308366 m n p) (@lem1308365 m n p)). Qed.
Lemma lem1308825 (A1 : nat) (A2 : nat) (n : nat) : (term29 A1 A2 n) = (term30 A1 A2 n).
Proof. exact (@lem1308824 A1 A2 n). Qed.
Lemma lem1308826 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1308827 (A1 : nat) (A2 : nat) (n : nat) : (term256 A1 A2 n) = (term257 A1 A2 n).
Proof. exact (MK_COMB (@lem1308826) (@lem1308825 A1 A2 n)). Qed.
Lemma lem1308828 (B1 : nat) (B2 : nat) : (Nat.add B1 B2) = (Nat.add B1 B2).
Proof. exact (eq_refl (Nat.add B1 B2)). Qed.
Lemma lem1308829 (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term255 A1 A2 n B1 B2) = (term258 A1 A2 n B1 B2).
Proof. exact (MK_COMB (@lem1308827 A1 A2 n) (@lem1308828 B1 B2)). Qed.
Lemma lem1308830 (x : nadd) (n : nat) : (term259 x n) = (term259 x n).
Proof. exact (eq_refl (term259 x n)). Qed.
Lemma lem1308831 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term260 x A1 A2 n B1 B2) = (term261 x A1 A2 n B1 B2).
Proof. exact (MK_COMB (@lem1308830 x n) (@lem1308829 A1 A2 n B1 B2)). Qed.
Lemma lem1308832 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term261 x A1 A2 n B1 B2) = (term260 x A1 A2 n B1 B2).
Proof. exact (SYM (@lem1308831 x A1 A2 n B1 B2)). Qed.
Lemma lem1308834 (a : nat) (c : nat) (b : nat) (d : nat) : (term20 a b c d) = (term20 a c b d).
Proof. exact (EQ_MP (@lem1308357 a c b d) (@lem0)). Qed.
Lemma lem1308835 (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : (term258 A1 A2 n B1 B2) = (term262 A1 B1 A2 n B2).
Proof. exact (@lem1308834 (Nat.mul A1 n) B1 (Nat.mul A2 n) B2). Qed.
Lemma lem1308836 (x : nadd) (n : nat) : (term259 x n) = (term259 x n).
Proof. exact (eq_refl (term259 x n)). Qed.
Lemma lem1308837 (x : nadd) (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : (term261 x A1 A2 n B1 B2) = (term263 x A1 B1 A2 n B2).
Proof. exact (MK_COMB (@lem1308836 x n) (@lem1308835 A1 B1 A2 n B2)). Qed.
Lemma lem1308838 (x : nadd) (A1 : nat) (A2 : nat) (n : nat) (B1 : nat) (B2 : nat) : (term263 x A1 B1 A2 n B2) = (term261 x A1 A2 n B1 B2).
Proof. exact (SYM (@lem1308837 x A1 B1 A2 n B2)). Qed.
Lemma lem1308840 (m : nat) (n : nat) (p : nat) (q : nat) : term11 m n p q.
Proof. exact (EQ_MP (@lem1308290 m n p q) (@lem1308289 m n p q)). Qed.
Lemma lem1308841 (x : nadd) (A1 : nat) (B1 : nat) (A2 : nat) (n : nat) (B2 : nat) : term264 x A1 B1 A2 n B2.
Proof. exact (@lem1308840 (term265 x n) (term266 x n) (term161 A1 n B1) (term161 A2 n B2)). Qed.
Lemma lem1308844 (n : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : term267 x A1 B1 n.
Proof. exact (@lem1308604 x A1 B1 h1 n). Qed.
Lemma lem1308845 (x : nadd) (A1 : nat) (n : nat) (B1 : nat) : (term267 x A1 B1 n) = (term268 x A1 n B1).
Proof. exact (eq_refl (term267 x A1 B1 n)). Qed.
Lemma lem1308846 (n : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : term268 x A1 n B1.
Proof. exact (EQ_MP (@lem1308845 x A1 n B1) (@lem1308844 n x A1 B1 h1)). Qed.
Lemma lem1308847 (x : nadd) (A1 : nat) (n : nat) (B1 : nat) : (term268 x A1 n B1) = ((term268 x A1 n B1) = True).
Proof. exact (@lem7 (term268 x A1 n B1)). Qed.
Lemma lem1308867 (n : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : (term268 x A1 n B1) = True.
Proof. exact (EQ_MP (@lem1308847 x A1 n B1) (@lem1308846 n x A1 B1 h1)). Qed.
Lemma lem1308868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1308869 (n : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : (term269 x A1 n B1) = (and True).
Proof. exact (MK_COMB (@lem1308868) (@lem1308867 n x A1 B1 h1)). Qed.
Lemma lem1308870 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term270 x A2 n B2) = (term270 x A2 n B2).
Proof. exact (eq_refl (term270 x A2 n B2)). Qed.
Lemma lem1308871 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : (term271 A1 B1 x A2 n B2) = (term272 x A2 n B2).
Proof. exact (MK_COMB (@lem1308869 n x A1 B1 h1) (@lem1308870 x A2 n B2)). Qed.
Lemma lem1308873 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1308874 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term272 x A2 n B2) = (term270 x A2 n B2).
Proof. exact (@lem1308873 (term270 x A2 n B2)). Qed.
Lemma lem1308875 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : (term271 A1 B1 x A2 n B2) = (term270 x A2 n B2).
Proof. exact (TRANS (@lem1308871 A2 n B2 x A1 B1 h1) (@lem1308874 x A2 n B2)). Qed.
Lemma lem1308876 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (A1 : nat) (B1 : nat) (h1 : term175 x A1 B1) : (term270 x A2 n B2) = (term271 A1 B1 x A2 n B2).
Proof. exact (SYM (@lem1308875 A2 n B2 x A1 B1 h1)). Qed.
Lemma lem1308878 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1308253 n m) (@lem1308252 m n)). Qed.
Lemma lem1308879 (x : nadd) (n : nat) : (term273 x n) = (term274 x n).
Proof. exact (@lem1308878 (dest_nadd x n) (term275 x n)). Qed.
Lemma lem1308880 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1308881 (x : nadd) (n : nat) : (term276 x n) = (term277 x n).
Proof. exact (MK_COMB (@lem1308880) (@lem1308879 x n)). Qed.
Lemma lem1308882 (n : nat) : (Nat.mul n n) = (Nat.mul n n).
Proof. exact (eq_refl (Nat.mul n n)). Qed.
Lemma lem1308883 (x : nadd) (n : nat) : (term278 x n) = (term279 x n).
Proof. exact (MK_COMB (@lem1308881 x n) (@lem1308882 n)). Qed.
Lemma lem1308884 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1308885 (x : nadd) (n : nat) : (term266 x n) = (term280 x n).
Proof. exact (MK_COMB (@lem1308884) (@lem1308883 x n)). Qed.
Lemma lem1308886 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308887 (x : nadd) (n : nat) : (term281 x n) = (term282 x n).
Proof. exact (MK_COMB (@lem1308886) (@lem1308885 x n)). Qed.
Lemma lem1308888 (A2 : nat) (n : nat) (B2 : nat) : (term161 A2 n B2) = (term161 A2 n B2).
Proof. exact (eq_refl (term161 A2 n B2)). Qed.
Lemma lem1308889 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term270 x A2 n B2) = (term283 x A2 n B2).
Proof. exact (MK_COMB (@lem1308887 x n) (@lem1308888 A2 n B2)). Qed.
Lemma lem1308890 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term283 x A2 n B2) = (term270 x A2 n B2).
Proof. exact (SYM (@lem1308889 x A2 n B2)). Qed.
Lemma lem1308891 (x : nadd) : term284 x.
Proof. exact (@lem1308248 x). Qed.
Lemma lem1308892 (x : nadd) : (term284 x) = ((term285 x) = (term286 x)).
Proof. exact (eq_refl (term284 x)). Qed.
Lemma lem1308894 (x : nadd) : term287 x.
Proof. exact (@lem82 (term288 x)). Qed.
Lemma lem1308911 (n : nat) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term204 x A2 B2) : term289 x A2 B2 n.
Proof. exact (@lem1308685 x A2 B2 h1 n). Qed.
Lemma lem1308912 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term289 x A2 B2 n) = (term217 x A2 n B2).
Proof. exact (eq_refl (term289 x A2 B2 n)). Qed.
Lemma lem1308913 (n : nat) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term204 x A2 B2) : term217 x A2 n B2.
Proof. exact (EQ_MP (@lem1308912 x A2 n B2) (@lem1308911 n x A2 B2 h1)). Qed.
Lemma lem1308914 (x : nadd) (A2 : nat) (n : nat) (B2 : nat) : (term217 x A2 n B2) = ((term217 x A2 n B2) = True).
Proof. exact (@lem7 (term217 x A2 n B2)). Qed.
Lemma lem1308917 (x : nadd) : (term285 x) = (term286 x).
Proof. exact (EQ_MP (@lem1308892 x) (@lem1308891 x)). Qed.
Lemma lem1308919 (x : nadd) (h1 : term112 x) : (term288 x) = False.
Proof. exact (@lem1308894 x (@lem1308512 x h1)). Qed.
Lemma lem1308920 : (@COND (nat -> nat)) = (@COND (nat -> nat)).
Proof. exact (eq_refl (@COND (nat -> nat))). Qed.
Lemma lem1308921 (x : nadd) (h1 : term112 x) : (term290 x) = (@COND (nat -> nat) False).
Proof. exact (MK_COMB (@lem1308920) (@lem1308919 x h1)). Qed.
Lemma lem1308922 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem1308923 (x : nadd) (h1 : term112 x) : (term292 x) = term293.
Proof. exact (MK_COMB (@lem1308921 x h1) (@lem1308922)). Qed.
Lemma lem1308924 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1308925 (x : nadd) (h1 : term112 x) : (term286 x) = (term294 x).
Proof. exact (MK_COMB (@lem1308923 x h1) (@lem1308924 x)). Qed.
Lemma lem1308927 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1308928 (t1 : nat -> nat) (t2 : nat -> nat) : (@COND (nat -> nat) False t1 t2) = t2.
Proof. exact (@lem1308927 (nat -> nat) t1 t2). Qed.
Lemma lem1308929 (x : nadd) : (term294 x) = (nadd_rinv x).
Proof. exact (@lem1308928 term291 (nadd_rinv x)). Qed.
Lemma lem1308930 (x : nadd) (h1 : term112 x) : (term286 x) = (nadd_rinv x).
Proof. exact (TRANS (@lem1308925 x h1) (@lem1308929 x)). Qed.
Lemma lem1308931 (x : nadd) (h1 : term112 x) : (term285 x) = (nadd_rinv x).
Proof. exact (TRANS (@lem1308917 x) (@lem1308930 x h1)). Qed.
Lemma lem1308932 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1308933 (n : nat) (x : nadd) (h1 : term112 x) : (term275 x n) = (nadd_rinv x n).
Proof. exact (MK_COMB (@lem1308931 x h1) (@lem1308932 n)). Qed.
Lemma lem1308934 (x : nadd) (n : nat) : (term295 x n) = (term295 x n).
Proof. exact (eq_refl (term295 x n)). Qed.
Lemma lem1308935 (n : nat) (x : nadd) (h1 : term112 x) : (term274 x n) = (term296 x n).
Proof. exact (MK_COMB (@lem1308934 x n) (@lem1308933 n x h1)). Qed.
Lemma lem1308936 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1308937 (n : nat) (x : nadd) (h1 : term112 x) : (term277 x n) = (term297 x n).
Proof. exact (MK_COMB (@lem1308936) (@lem1308935 n x h1)). Qed.
Lemma lem1308938 (n : nat) : (Nat.mul n n) = (Nat.mul n n).
Proof. exact (eq_refl (Nat.mul n n)). Qed.
Lemma lem1308939 (n : nat) (x : nadd) (h1 : term112 x) : (term279 x n) = (term298 x n).
Proof. exact (MK_COMB (@lem1308937 n x h1) (@lem1308938 n)). Qed.
Lemma lem1308940 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1308941 (n : nat) (x : nadd) (h1 : term112 x) : (term280 x n) = (term209 x n).
Proof. exact (MK_COMB (@lem1308940) (@lem1308939 n x h1)). Qed.
Lemma lem1308942 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1308943 (n : nat) (x : nadd) (h1 : term112 x) : (term282 x n) = (term211 x n).
Proof. exact (MK_COMB (@lem1308942) (@lem1308941 n x h1)). Qed.
Lemma lem1308944 (A2 : nat) (n : nat) (B2 : nat) : (term161 A2 n B2) = (term161 A2 n B2).
Proof. exact (eq_refl (term161 A2 n B2)). Qed.
Lemma lem1308945 (A2 : nat) (n : nat) (B2 : nat) (x : nadd) (h1 : term112 x) : (term283 x A2 n B2) = (term217 x A2 n B2).
Proof. exact (MK_COMB (@lem1308943 n x h1) (@lem1308944 A2 n B2)). Qed.
Lemma lem1308947 (n : nat) (x : nadd) (A2 : nat) (B2 : nat) (h1 : term204 x A2 B2) : (term217 x A2 n B2) = True.
Proof. exact (EQ_MP (@lem1308914 x A2 n B2) (@lem1308913 n x A2 B2 h1)). Qed.
Lemma lem1308948 (n : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term204 x A2 B2) (h2 : term112 x) : (term283 x A2 n B2) = True.
Proof. exact (TRANS (@lem1308945 A2 n B2 x h2) (@lem1308947 n x A2 B2 h1)). Qed.
Lemma lem1308949 (n : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term204 x A2 B2) (h2 : term112 x) : True = (term283 x A2 n B2).
Proof. exact (SYM (@lem1308948 n A2 B2 x h1 h2)). Qed.
Lemma lem1308950 (n : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term204 x A2 B2) (h2 : term112 x) : term283 x A2 n B2.
Proof. exact (EQ_MP (@lem1308949 n A2 B2 x h1 h2) (@lem0)). Qed.
Lemma lem1308951 (n : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term204 x A2 B2) (h2 : term112 x) : term270 x A2 n B2.
Proof. exact (EQ_MP (@lem1308890 x A2 n B2) (@lem1308950 n A2 B2 x h1 h2)). Qed.
Lemma lem1308952 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term271 A1 B1 x A2 n B2.
Proof. exact (EQ_MP (@lem1308876 A2 n B2 x A1 B1 h1) (@lem1308951 n A2 B2 x h2 h3)). Qed.
Lemma lem1308953 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term263 x A1 B1 A2 n B2.
Proof. exact (@lem1308841 x A1 B1 A2 n B2 (@lem1308952 n A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308954 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term261 x A1 A2 n B1 B2.
Proof. exact (EQ_MP (@lem1308838 x A1 A2 n B1 B2) (@lem1308953 n A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308955 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term260 x A1 A2 n B1 B2.
Proof. exact (EQ_MP (@lem1308832 x A1 A2 n B1 B2) (@lem1308954 n A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308956 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term299 x A1 A2 n B1 B2.
Proof. exact (ex_intro (term300 x A1 A2 n B1 B2) (term273 x n) (@lem1308955 n A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308957 (n : nat) (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term301 x A1 A2 n B1 B2.
Proof. exact (@lem1308822 x A1 A2 n B1 B2 (@lem1308956 n A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308962 (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term302 x A1 A2 B1 B2.
Proof. exact (fun n : nat => @lem1308957 n A1 B1 A2 B2 x h1 h2 h3). Qed.
Lemma lem1308963 (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term303 x A1 A2.
Proof. exact (ex_intro (term304 x A1 A2) (Nat.add B1 B2) (@lem1308962 A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308964 (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term198 x.
Proof. exact (ex_intro (term197 x) (Nat.add A1 A2) (@lem1308963 A1 B1 A2 B2 x h1 h2 h3)). Qed.
Lemma lem1308965 (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : (term204 x A2 B2) = (term198 x).
Proof. exact (prop_ext (fun h4 : term204 x A2 B2 => @lem1308964 A1 B1 A2 B2 x h1 h2 h3) (fun h4 : term198 x => @lem1308685 x A2 B2 h2)). Qed.
Lemma lem1308966 (A1 : nat) (B1 : nat) (A2 : nat) (B2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term204 x A2 B2) (h3 : term112 x) : term198 x.
Proof. exact (EQ_MP (@lem1308965 A1 B1 A2 B2 x h1 h2 h3) (@lem1308685 x A2 B2 h2)). Qed.
Lemma lem1308967 (A1 : nat) (B1 : nat) (A2 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term203 x A2) (h3 : term112 x) : term198 x.
Proof. exact (ex_elim (@lem1308684 x A2 h2) (fun B2 : nat => fun h0 : term222 x A2 B2 => @lem1308966 A1 B1 A2 B2 x h1 h0 h3)). Qed.
Lemma lem1308968 (A1 : nat) (B1 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term202 x) (h3 : term112 x) : term198 x.
Proof. exact (ex_elim (@lem1308683 x h2) (fun A2 : nat => fun h0 : term252 x A2 => @lem1308967 A1 B1 A2 x h1 h0 h3)). Qed.
Lemma lem1308969 (A1 : nat) (B1 : nat) (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term201 x A' B') (h3 : term200 N x) (h4 : term112 x) : (term202 x) = (term198 x).
Proof. exact (prop_ext (fun h5 : term202 x => @lem1308968 A1 B1 x h1 h5 h4) (fun h5 : term198 x => @lem1308819 A' B' N x h2 h3)). Qed.
Lemma lem1308970 (A1 : nat) (B1 : nat) (A' : nat) (B' : nat) (N : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term201 x A' B') (h3 : term200 N x) (h4 : term112 x) : term198 x.
Proof. exact (EQ_MP (@lem1308969 A1 B1 A' B' N x h1 h2 h3 h4) (@lem1308819 A' B' N x h2 h3)). Qed.
Lemma lem1308971 (A1 : nat) (B1 : nat) (N : nat) (A' : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term200 N x) (h3 : term77 x A') (h4 : term112 x) : term198 x.
Proof. exact (ex_elim (@lem1308440 x A' h3) (fun B' : nat => fun h0 : term305 x A' B' => @lem1308970 A1 B1 A' B' N x h1 h0 h2 h4)). Qed.
Lemma lem1308972 (A1 : nat) (B1 : nat) (N : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term200 N x) (h3 : term112 x) : term198 x.
Proof. exact (ex_elim (@lem1308439 x) (fun A' : nat => fun h0 : term306 x A' => @lem1308971 A1 B1 N A' x h1 h2 h0 h3)). Qed.
Lemma lem1308973 (A1 : nat) (B1 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term112 x) : term198 x.
Proof. exact (ex_elim (@lem1308680 x h2) (fun N : nat => fun h0 : term307 x N => @lem1308972 A1 B1 N x h1 h0 h2)). Qed.
Lemma lem1308974 (A1 : nat) (B1 : nat) (x : nadd) (h1 : term175 x A1 B1) (h2 : term112 x) : term174 x.
Proof. exact (EQ_MP (@lem1308675 x) (@lem1308973 A1 B1 x h1 h2)). Qed.
Lemma lem1308975 (A1 : nat) (x : nadd) (h1 : term99 x A1) (h2 : term112 x) : term174 x.
Proof. exact (ex_elim (@lem1308496 x A1 h1) (fun B1 : nat => fun h0 : term308 x A1 B1 => @lem1308974 A1 B1 x h0 h2)). Qed.
Lemma lem1308976 (x : nadd) (h1 : term112 x) : term174 x.
Proof. exact (ex_elim (@lem1308495 x) (fun A1 : nat => fun h0 : term309 x A1 => @lem1308975 A1 x h0 h1)). Qed.
Lemma lem1308977 (x : nadd) (h1 : term112 x) : term145 x.
Proof. exact (EQ_MP (@lem1308603 x) (@lem1308976 x h1)). Qed.
Lemma lem1308978 (x : nadd) (h1 : term112 x) : term113 x.
Proof. exact (EQ_MP (@lem1308568 x) (@lem1308977 x h1)). Qed.
Lemma lem1308979 (x : nadd) : term310 x.
Proof. exact (fun h0 : term112 x => @lem1308978 x h0). Qed.
Lemma lem1308984 : term311.
Proof. exact (fun x : nadd => @lem1308979 x). Qed.
