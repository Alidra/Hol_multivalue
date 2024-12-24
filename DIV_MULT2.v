Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MULT2_term_abbrevs.
Require Import DIVISION_spec.
Require Import DIV_UNIQ_spec.
Require Import DIV_ZERO_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem184266 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem184267 (n : nat) (h1 : n = (NUMERAL 0)) : (NUMERAL 0) = n.
Proof. exact (SYM (@lem184266 n h1)). Qed.
Lemma lem184268 (n : nat) (h1 : (NUMERAL 0) = n) : (NUMERAL 0) = n.
Proof. exact (h1). Qed.
Lemma lem184269 (n : nat) (h1 : (NUMERAL 0) = n) : n = (NUMERAL 0).
Proof. exact (SYM (@lem184268 n h1)). Qed.
Lemma lem184270 (n : nat) : (n = (NUMERAL 0)) = ((NUMERAL 0) = n).
Proof. exact (prop_ext (fun h1 : n = (NUMERAL 0) => @lem184267 n h1) (fun h1 : (NUMERAL 0) = n => @lem184269 n h1)). Qed.
Lemma lem184271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184272 (n : nat) : (term0 n) = (term1 n).
Proof. exact (MK_COMB (@lem184271) (@lem184270 n)). Qed.
Lemma lem184273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem184274 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem184273) (@lem184272 n)). Qed.
Lemma lem184276 (m : nat) (n : nat) (h1 : m = (term4 m n)) : m = (term4 m n).
Proof. exact (h1). Qed.
Lemma lem184277 (m : nat) (n : nat) (h1 : m = (term4 m n)) : (term4 m n) = m.
Proof. exact (SYM (@lem184276 m n h1)). Qed.
Lemma lem184278 (n : nat) (m : nat) (h1 : (term4 m n) = m) : (term4 m n) = m.
Proof. exact (h1). Qed.
Lemma lem184279 (n : nat) (m : nat) (h1 : (term4 m n) = m) : m = (term4 m n).
Proof. exact (SYM (@lem184278 n m h1)). Qed.
Lemma lem184280 (n : nat) (m : nat) : (m = (term4 m n)) = ((term4 m n) = m).
Proof. exact (prop_ext (fun h1 : m = (term4 m n) => @lem184277 m n h1) (fun h1 : (term4 m n) = m => @lem184279 n m h1)). Qed.
Lemma lem184281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem184282 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem184281) (@lem184280 n m)). Qed.
Lemma lem184284 (m : nat) (n : nat) : (term7 m n) = (term7 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem184285 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem184282 n m) (@lem184284 m n)). Qed.
Lemma lem184286 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem184274 n) (@lem184285 m n)). Qed.
Lemma lem184287 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem184286 m n)). Qed.
Lemma lem184288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184289 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem184288) (@lem184287 m)). Qed.
Lemma lem184290 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem184289 m)). Qed.
Lemma lem184291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184292 : term18 = term19.
Proof. exact (MK_COMB (@lem184291) (@lem184290)). Qed.
Lemma lem184293 : term19.
Proof. exact (EQ_MP (@lem184292) (@lem157261)). Qed.
Lemma lem184297 (n : nat) (m : nat) (p : nat) (h1 : (term20 m n p) = (term21 n m p)) : (term20 m n p) = (term21 n m p).
Proof. exact (h1). Qed.
Lemma lem184298 (n : nat) (m : nat) (p : nat) (h1 : (term20 m n p) = (term21 n m p)) : (term21 n m p) = (term20 m n p).
Proof. exact (SYM (@lem184297 n m p h1)). Qed.
Lemma lem184299 (m : nat) (n : nat) (p : nat) (h1 : (term21 n m p) = (term20 m n p)) : (term21 n m p) = (term20 m n p).
Proof. exact (h1). Qed.
Lemma lem184300 (m : nat) (n : nat) (p : nat) (h1 : (term21 n m p) = (term20 m n p)) : (term20 m n p) = (term21 n m p).
Proof. exact (SYM (@lem184299 m n p h1)). Qed.
Lemma lem184301 (m : nat) (n : nat) (p : nat) : ((term20 m n p) = (term21 n m p)) = ((term21 n m p) = (term20 m n p)).
Proof. exact (prop_ext (fun h1 : (term20 m n p) = (term21 n m p) => @lem184298 n m p h1) (fun h1 : (term21 n m p) = (term20 m n p) => @lem184300 m n p h1)). Qed.
Lemma lem184302 (m : nat) (n : nat) : (term22 n m) = (term23 m n).
Proof. exact (fun_ext (fun p : nat => @lem184301 m n p)). Qed.
Lemma lem184303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184304 (m : nat) (n : nat) : (term24 n m) = (term25 m n).
Proof. exact (MK_COMB (@lem184303) (@lem184302 m n)). Qed.
Lemma lem184305 (m : nat) : (term26 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem184304 m n)). Qed.
Lemma lem184306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184307 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem184306) (@lem184305 m)). Qed.
Lemma lem184308 : term30 = term31.
Proof. exact (fun_ext (fun m : nat => @lem184307 m)). Qed.
Lemma lem184309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem184310 : term32 = term33.
Proof. exact (MK_COMB (@lem184309) (@lem184308)). Qed.
Lemma lem184311 : term33.
Proof. exact (EQ_MP (@lem184310) (@lem82055)). Qed.
Lemma lem184312 (m : nat) : term34 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem184313 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem184314 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem184313 m) (@lem184312 m)). Qed.
Lemma lem184315 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem184314 m n). Qed.
Lemma lem184316 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem184317 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem184316 m n) (@lem184315 m n)). Qed.
Lemma lem184318 (m : nat) (n : nat) (p : nat) : term38 m n p.
Proof. exact (@lem184317 m n p). Qed.
Lemma lem184319 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term39 m n p)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem184321 (m : nat) : term40 m.
Proof. exact (@lem184311 m). Qed.
Lemma lem184322 (m : nat) : (term40 m) = (term29 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem184323 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem184322 m) (@lem184321 m)). Qed.
Lemma lem184324 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem184323 m n). Qed.
Lemma lem184325 (m : nat) (n : nat) : (term41 m n) = (term25 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem184326 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem184325 m n) (@lem184324 m n)). Qed.
Lemma lem184327 (m : nat) (n : nat) (p : nat) : term42 m n p.
Proof. exact (@lem184326 m n p). Qed.
Lemma lem184328 (m : nat) (n : nat) (p : nat) : (term42 m n p) = ((term21 n m p) = (term20 m n p)).
Proof. exact (eq_refl (term42 m n p)). Qed.
Lemma lem184330 {A : Type'} (x : A) : term43 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem184331 {A : Type'} (x : A) : (term43 A x) = ((x = x) = True).
Proof. exact (eq_refl (term43 A x)). Qed.
Lemma lem184333 (n : nat) (m : nat) (p : nat) : term44 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem184349 (n : nat) (m : nat) (p : nat) : (term45 m n p) = (term45 n m p).
Proof. exact (proj2 (@lem184333 n m p)). Qed.
Lemma lem184350 (a : nat) (b : nat) (c : nat) : (term45 b a c) = (term45 a b c).
Proof. exact (@lem184349 a b c). Qed.
Lemma lem184360 (a : nat) (b : nat) (c : nat) : (term46 a b c) = (term46 a b c).
Proof. exact (eq_refl (term46 a b c)). Qed.
Lemma lem184361 (a : nat) (b : nat) (c : nat) : ((term45 a b c) = (term45 b a c)) = ((term45 a b c) = (term45 a b c)).
Proof. exact (MK_COMB (@lem184360 a b c) (@lem184350 a b c)). Qed.
Lemma lem184363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem184331 A x) (@lem184330 A x)). Qed.
Lemma lem184364 (x : nat) : (x = x) = True.
Proof. exact (@lem184363 nat x). Qed.
Lemma lem184365 (a : nat) (b : nat) (c : nat) : ((term45 a b c) = (term45 a b c)) = True.
Proof. exact (@lem184364 (term45 a b c)). Qed.
Lemma lem184366 (b : nat) (a : nat) (c : nat) : ((term45 a b c) = (term45 b a c)) = True.
Proof. exact (TRANS (@lem184361 a b c) (@lem184365 a b c)). Qed.
Lemma lem184367 (b : nat) (a : nat) (c : nat) : True = ((term45 a b c) = (term45 b a c)).
Proof. exact (SYM (@lem184366 b a c)). Qed.
Lemma lem184369 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem184370 (m : nat) (h1 : term47) : term48 m.
Proof. exact (@lem184369 h1 m). Qed.
Lemma lem184371 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem184372 (m : nat) (h1 : term47) : term49 m.
Proof. exact (EQ_MP (@lem184371 m) (@lem184370 m h1)). Qed.
Lemma lem184373 (m : nat) (n : nat) (h1 : term47) : term50 m n.
Proof. exact (@lem184372 m h1 n). Qed.
Lemma lem184374 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem184375 (m : nat) (n : nat) (h1 : term47) : term51 m n.
Proof. exact (EQ_MP (@lem184374 m n) (@lem184373 m n h1)). Qed.
Lemma lem184376 (m : nat) (n : nat) (q : nat) (h1 : term47) : term52 m n q.
Proof. exact (@lem184375 m n h1 q). Qed.
Lemma lem184377 (m : nat) (n : nat) (q : nat) : (term52 m n q) = (term53 m n q).
Proof. exact (eq_refl (term52 m n q)). Qed.
Lemma lem184378 (m : nat) (n : nat) (q : nat) (h1 : term47) : term53 m n q.
Proof. exact (EQ_MP (@lem184377 m n q) (@lem184376 m n q h1)). Qed.
Lemma lem184379 (m : nat) (n : nat) (q : nat) (r : nat) (h1 : term47) : term54 m n q r.
Proof. exact (@lem184378 m n q h1 r). Qed.
Lemma lem184380 (r : nat) (m : nat) (n : nat) (q : nat) : (term54 m n q r) = (term55 r m n q).
Proof. exact (eq_refl (term54 m n q r)). Qed.
Lemma lem184381 (r : nat) (m : nat) (n : nat) (q : nat) (h1 : term47) : term55 r m n q.
Proof. exact (EQ_MP (@lem184380 r m n q) (@lem184379 m n q r h1)). Qed.
Lemma lem184382 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term56 m q r n) : term56 m q r n.
Proof. exact (h1). Qed.
Lemma lem184383 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term47) (h2 : term56 m q r n) : (Nat.div m n) = q.
Proof. exact (@lem184381 r m n q h1 (@lem184382 m q r n h2)). Qed.
Lemma lem184384 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term56 m q r n) : term57 m n q.
Proof. exact (fun h0 : term47 => @lem184383 m q r n h0 h1). Qed.
Lemma lem184385 (m : nat) (q : nat) (n : nat) (h1 : term58 m q n) : term58 m q n.
Proof. exact (h1). Qed.
Lemma lem184386 (m : nat) (q : nat) (n : nat) (h1 : term58 m q n) : term57 m n q.
Proof. exact (ex_elim (@lem184385 m q n h1) (fun r : nat => fun h0 : term59 m q n r => @lem184384 m q r n h0)). Qed.
Lemma lem184387 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem184388 (m : nat) (q : nat) (n : nat) (h1 : term47) (h2 : term58 m q n) : (Nat.div m n) = q.
Proof. exact (@lem184386 m q n h2 (@lem184387 h1)). Qed.
Lemma lem184389 (m : nat) (n : nat) (q : nat) (h1 : term47) : term60 m n q.
Proof. exact (fun h0 : term58 m q n => @lem184388 m q n h1 h0). Qed.
Lemma lem184390 (m : nat) (n : nat) (h1 : term47) : term61 m n.
Proof. exact (fun q : nat => @lem184389 m n q h1). Qed.
Lemma lem184391 (m : nat) (h1 : term47) : term62 m.
Proof. exact (fun n : nat => @lem184390 m n h1). Qed.
Lemma lem184392 (h1 : term47) : term63.
Proof. exact (fun m : nat => @lem184391 m h1). Qed.
Lemma lem184393 : term64.
Proof. exact (fun h0 : term47 => @lem184392 h0). Qed.
Lemma lem184394 : term63.
Proof. exact (@lem184393 (@lem169759)). Qed.
Lemma lem184395 (m : nat) : term65 m.
Proof. exact (@lem184394 m). Qed.
Lemma lem184396 (m : nat) : (term65 m) = (term62 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem184397 (m : nat) : term62 m.
Proof. exact (EQ_MP (@lem184396 m) (@lem184395 m)). Qed.
Lemma lem184398 (m : nat) (n : nat) : term66 m n.
Proof. exact (@lem184397 m n). Qed.
Lemma lem184399 (m : nat) (n : nat) : (term66 m n) = (term61 m n).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem184400 (m : nat) (n : nat) : term61 m n.
Proof. exact (EQ_MP (@lem184399 m n) (@lem184398 m n)). Qed.
Lemma lem184401 (m : nat) (n : nat) (q : nat) : term67 m n q.
Proof. exact (@lem184400 m n q). Qed.
Lemma lem184402 (m : nat) (n : nat) (q : nat) : (term67 m n q) = (term60 m n q).
Proof. exact (eq_refl (term67 m n q)). Qed.
Lemma lem184404 (p : nat) : term68 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem184405 (p : nat) : (term68 p) = (term69 p).
Proof. exact (eq_refl (term68 p)). Qed.
Lemma lem184406 (p : nat) : term69 p.
Proof. exact (EQ_MP (@lem184405 p) (@lem184404 p)). Qed.
Lemma lem184408 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem184409 (m : nat) (h1 : term0 m) : term0 m.
Proof. exact (h1). Qed.
Lemma lem184410 : term70.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem184436 : term71.
Proof. exact (proj1 (@lem184410)). Qed.
Lemma lem184437 (m : nat) : term72 m.
Proof. exact (@lem184436 m). Qed.
Lemma lem184438 (m : nat) : (term72 m) = ((term73 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term72 m)). Qed.
Lemma lem184444 (n : nat) : term74 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem184445 (n : nat) : (term74 n) = ((term75 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem184463 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem184464 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem184465 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul m p) = (term73 m).
Proof. exact (MK_COMB (@lem184464 m) (@lem184463 p h1)). Qed.
Lemma lem184467 (m : nat) : (term73 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem184438 m) (@lem184437 m)). Qed.
Lemma lem184468 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem184465 m p h1) (@lem184467 m)). Qed.
Lemma lem184469 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem184470 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (term78 m n).
Proof. exact (MK_COMB (@lem184469 m n) (@lem184468 m p h1)). Qed.
Lemma lem184472 (n : nat) : (term75 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem184445 n) (@lem184444 n)). Qed.
Lemma lem184473 (m : nat) (n : nat) : (term78 m n) = (NUMERAL 0).
Proof. exact (@lem184472 (Nat.mul m n)). Qed.
Lemma lem184474 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem184470 m n p h1) (@lem184473 m n)). Qed.
Lemma lem184475 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem184476 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term79 n m p) = term80.
Proof. exact (MK_COMB (@lem184475) (@lem184474 n m p h1)). Qed.
Lemma lem184478 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem184479 (n : nat) : (Nat.div n) = (Nat.div n).
Proof. exact (eq_refl (Nat.div n)). Qed.
Lemma lem184480 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (term75 n).
Proof. exact (MK_COMB (@lem184479 n) (@lem184478 p h1)). Qed.
Lemma lem184482 (n : nat) : (term75 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem184445 n) (@lem184444 n)). Qed.
Lemma lem184483 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.div n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem184480 n p h1) (@lem184482 n)). Qed.
Lemma lem184484 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term77 n m p) = (Nat.div n p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem184476 n m p h1) (@lem184483 n p h1)). Qed.
Lemma lem184486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem184487 (x : nat) : (x = x) = True.
Proof. exact (@lem184486 nat x). Qed.
Lemma lem184488 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem184487 (NUMERAL 0)). Qed.
Lemma lem184489 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term77 n m p) = (Nat.div n p)) = True.
Proof. exact (TRANS (@lem184484 m n p h1) (@lem184488)). Qed.
Lemma lem184490 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = ((term77 n m p) = (Nat.div n p)).
Proof. exact (SYM (@lem184489 m n p h1)). Qed.
Lemma lem184491 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (Nat.div n p).
Proof. exact (EQ_MP (@lem184490 m n p h1) (@lem0)). Qed.
Lemma lem184560 (m : nat) (n : nat) (q : nat) : term60 m n q.
Proof. exact (EQ_MP (@lem184402 m n q) (@lem184401 m n q)). Qed.
Lemma lem184561 (m : nat) (n : nat) (p : nat) : term81 m n p.
Proof. exact (@lem184560 (Nat.mul m n) (Nat.mul m p) (Nat.div n p)). Qed.
Lemma lem184562 (m : nat) : term82 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem184563 (m : nat) : (term82 m) = (term14 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem184564 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem184563 m) (@lem184562 m)). Qed.
Lemma lem184565 (m : nat) (n : nat) : term83 m n.
Proof. exact (@lem184564 m n). Qed.
Lemma lem184566 (m : nat) (n : nat) : (term83 m n) = (term10 m n).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem184567 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem184566 m n) (@lem184565 m n)). Qed.
Lemma lem184568 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem184569 (m : nat) (n : nat) (h1 : term0 n) : term8 m n.
Proof. exact (@lem184567 m n (@lem184568 n h1)). Qed.
Lemma lem184570 (m : nat) (n : nat) (h1 : term0 n) : term7 m n.
Proof. exact (proj2 (@lem184569 m n h1)). Qed.
Lemma lem184571 (m : nat) (n : nat) : (term7 m n) = ((term7 m n) = True).
Proof. exact (@lem7 (term7 m n)). Qed.
Lemma lem184572 (m : nat) (n : nat) (h1 : term0 n) : (term7 m n) = True.
Proof. exact (EQ_MP (@lem184571 m n) (@lem184570 m n h1)). Qed.
Lemma lem184589 (m : nat) : term84 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem184590 (m : nat) : (term84 m) = (term85 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem184591 (m : nat) : term85 m.
Proof. exact (EQ_MP (@lem184590 m) (@lem184589 m)). Qed.
Lemma lem184592 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem184591 m n). Qed.
Lemma lem184593 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem184594 (m : nat) (n : nat) : term87 m n.
Proof. exact (EQ_MP (@lem184593 m n) (@lem184592 m n)). Qed.
Lemma lem184595 (m : nat) (n : nat) (p : nat) : term88 m n p.
Proof. exact (@lem184594 m n p). Qed.
Lemma lem184596 (m : nat) (n : nat) (p : nat) : (term88 m n p) = ((term89 n m p) = (term90 m n p)).
Proof. exact (eq_refl (term88 m n p)). Qed.
Lemma lem184598 (m : nat) : term91 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem184611 (p : nat) : term91 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem184701 (m : nat) (n : nat) (p : nat) : (term89 n m p) = (term90 m n p).
Proof. exact (EQ_MP (@lem184596 m n p) (@lem184595 m n p)). Qed.
Lemma lem184702 (m : nat) (n : nat) (p : nat) : (term92 n m p) = (term93 m n p).
Proof. exact (@lem184701 m (Nat.modulo n p) p). Qed.
Lemma lem184716 (m : nat) (h1 : term0 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem184598 m (@lem184409 m h1)). Qed.
Lemma lem184719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184720 (m : nat) (h1 : term0 m) : (term0 m) = (~ False).
Proof. exact (MK_COMB (@lem184719) (@lem184716 m h1)). Qed.
Lemma lem184722 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem184725 (m : nat) (h1 : term0 m) : (term0 m) = True.
Proof. exact (TRANS (@lem184720 m h1) (@lem184722)). Qed.
Lemma lem184726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem184727 (m : nat) (h1 : term0 m) : (term94 m) = (and True).
Proof. exact (MK_COMB (@lem184726) (@lem184725 m h1)). Qed.
Lemma lem184735 (m : nat) (n : nat) : term95 m n.
Proof. exact (fun h0 : term0 n => @lem184572 m n h0). Qed.
Lemma lem184736 (n : nat) (p : nat) : term95 n p.
Proof. exact (@lem184735 n p). Qed.
Lemma lem184742 (p : nat) (h1 : term0 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem184611 p (@lem184408 p h1)). Qed.
Lemma lem184745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184746 (p : nat) (h1 : term0 p) : (term0 p) = (~ False).
Proof. exact (MK_COMB (@lem184745) (@lem184742 p h1)). Qed.
Lemma lem184748 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem184751 (p : nat) (h1 : term0 p) : (term0 p) = True.
Proof. exact (TRANS (@lem184746 p h1) (@lem184748)). Qed.
Lemma lem184752 (p : nat) (h1 : term0 p) : True = (term0 p).
Proof. exact (SYM (@lem184751 p h1)). Qed.
Lemma lem184753 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (EQ_MP (@lem184752 p h1) (@lem0)). Qed.
Lemma lem184754 (n : nat) (p : nat) (h1 : term0 p) : (term7 n p) = True.
Proof. exact (@lem184736 n p (@lem184753 p h1)). Qed.
Lemma lem184757 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term93 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem184727 m h1) (@lem184754 n p h2)). Qed.
Lemma lem184759 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem184760 : (True /\ True) = True.
Proof. exact (@lem184759 True). Qed.
Lemma lem184763 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term93 m n p) = True.
Proof. exact (TRANS (@lem184757 n m p h1 h2) (@lem184760)). Qed.
Lemma lem184764 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term92 n m p) = True.
Proof. exact (TRANS (@lem184702 m n p) (@lem184763 n m p h1 h2)). Qed.
Lemma lem184765 (m : nat) (n : nat) (p : nat) : (term96 m n p) = (term96 m n p).
Proof. exact (eq_refl (term96 m n p)). Qed.
Lemma lem184766 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term97 n m p) = (term98 m n p).
Proof. exact (MK_COMB (@lem184765 m n p) (@lem184764 n m p h1 h2)). Qed.
Lemma lem184768 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem184769 (m : nat) (n : nat) (p : nat) : (term98 m n p) = ((Nat.mul m n) = (term99 m n p)).
Proof. exact (@lem184768 ((Nat.mul m n) = (term99 m n p))). Qed.
Lemma lem184838 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term97 n m p) = ((Nat.mul m n) = (term99 m n p)).
Proof. exact (TRANS (@lem184766 n m p h1 h2) (@lem184769 m n p)). Qed.
Lemma lem184839 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : ((Nat.mul m n) = (term99 m n p)) = (term97 n m p).
Proof. exact (SYM (@lem184838 n m p h1 h2)). Qed.
Lemma lem184843 (b : nat) (a : nat) (c : nat) : (term45 a b c) = (term45 b a c).
Proof. exact (EQ_MP (@lem184367 b a c) (@lem0)). Qed.
Lemma lem184844 (m : nat) (n : nat) (p : nat) : (term100 n m p) = (term101 m n p).
Proof. exact (@lem184843 m (Nat.div n p) p). Qed.
Lemma lem184845 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem184846 (m : nat) (n : nat) (p : nat) : (term102 n m p) = (term103 m n p).
Proof. exact (MK_COMB (@lem184845) (@lem184844 m n p)). Qed.
Lemma lem184847 (m : nat) (n : nat) (p : nat) : (term104 m n p) = (term104 m n p).
Proof. exact (eq_refl (term104 m n p)). Qed.
Lemma lem184848 (m : nat) (n : nat) (p : nat) : (term99 m n p) = (term105 m n p).
Proof. exact (MK_COMB (@lem184846 m n p) (@lem184847 m n p)). Qed.
Lemma lem184849 (m : nat) (n : nat) : (term106 m n) = (term106 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem184850 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term99 m n p)) = ((Nat.mul m n) = (term105 m n p)).
Proof. exact (MK_COMB (@lem184849 m n) (@lem184848 m n p)). Qed.
Lemma lem184851 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term105 m n p)) = ((Nat.mul m n) = (term99 m n p)).
Proof. exact (SYM (@lem184850 m n p)). Qed.
Lemma lem184855 (m : nat) (n : nat) (p : nat) : (term21 n m p) = (term20 m n p).
Proof. exact (EQ_MP (@lem184328 m n p) (@lem184327 m n p)). Qed.
Lemma lem184856 (m : nat) (n : nat) (p : nat) : (term105 m n p) = (term107 m n p).
Proof. exact (@lem184855 m (term108 n p) (Nat.modulo n p)). Qed.
Lemma lem184857 (m : nat) (n : nat) : (term106 m n) = (term106 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem184858 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term105 m n p)) = ((Nat.mul m n) = (term107 m n p)).
Proof. exact (MK_COMB (@lem184857 m n) (@lem184856 m n p)). Qed.
Lemma lem184860 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term39 m n p).
Proof. exact (EQ_MP (@lem184319 m n p) (@lem184318 m n p)). Qed.
Lemma lem184861 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term107 m n p)) = (term109 m n p).
Proof. exact (@lem184860 m n (term4 n p)). Qed.
Lemma lem184868 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term105 m n p)) = (term109 m n p).
Proof. exact (TRANS (@lem184858 m n p) (@lem184861 m n p)). Qed.
Lemma lem184869 (m : nat) (n : nat) (p : nat) : (term109 m n p) = ((Nat.mul m n) = (term105 m n p)).
Proof. exact (SYM (@lem184868 m n p)). Qed.
Lemma lem184870 (m : nat) : term110 m.
Proof. exact (@lem184293 m). Qed.
Lemma lem184871 (m : nat) : (term110 m) = (term15 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem184872 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem184871 m) (@lem184870 m)). Qed.
Lemma lem184873 (m : nat) (n : nat) : term111 m n.
Proof. exact (@lem184872 m n). Qed.
Lemma lem184874 (m : nat) (n : nat) : (term111 m n) = (term11 m n).
Proof. exact (eq_refl (term111 m n)). Qed.
Lemma lem184875 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem184874 m n) (@lem184873 m n)). Qed.
Lemma lem184876 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem184877 (m : nat) (n : nat) (h1 : term1 n) : term9 m n.
Proof. exact (@lem184875 m n (@lem184876 n h1)). Qed.
Lemma lem184886 (m : nat) (n : nat) (h1 : term1 n) : (term4 m n) = m.
Proof. exact (proj1 (@lem184877 m n h1)). Qed.
Lemma lem184892 (m : nat) : term91 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem184908 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem184909 (p : nat) (h1 : p = (NUMERAL 0)) : (NUMERAL 0) = p.
Proof. exact (SYM (@lem184908 p h1)). Qed.
Lemma lem184910 (p : nat) (h1 : (NUMERAL 0) = p) : (NUMERAL 0) = p.
Proof. exact (h1). Qed.
Lemma lem184911 (p : nat) (h1 : (NUMERAL 0) = p) : p = (NUMERAL 0).
Proof. exact (SYM (@lem184910 p h1)). Qed.
Lemma lem184912 (p : nat) : (p = (NUMERAL 0)) = ((NUMERAL 0) = p).
Proof. exact (prop_ext (fun h1 : p = (NUMERAL 0) => @lem184909 p h1) (fun h1 : (NUMERAL 0) = p => @lem184911 p h1)). Qed.
Lemma lem184913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184914 (p : nat) : (term0 p) = (term1 p).
Proof. exact (MK_COMB (@lem184913) (@lem184912 p)). Qed.
Lemma lem184915 (p : nat) (h1 : term0 p) : term1 p.
Proof. exact (EQ_MP (@lem184914 p) (@lem184408 p h1)). Qed.
Lemma lem184916 (p : nat) : term112 p.
Proof. exact (@lem82 ((NUMERAL 0) = p)). Qed.
Lemma lem184921 (m : nat) (h1 : term0 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem184892 m (@lem184409 m h1)). Qed.
Lemma lem184922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem184923 (m : nat) (h1 : term0 m) : (term113 m) = (or False).
Proof. exact (MK_COMB (@lem184922) (@lem184921 m h1)). Qed.
Lemma lem184927 (n : nat) (m : nat) : term114 n m.
Proof. exact (fun h0 : term1 n => @lem184886 m n h0). Qed.
Lemma lem184928 (p : nat) (n : nat) : term114 p n.
Proof. exact (@lem184927 p n). Qed.
Lemma lem184930 (p : nat) (h1 : term0 p) : ((NUMERAL 0) = p) = False.
Proof. exact (@lem184916 p (@lem184915 p h1)). Qed.
Lemma lem184931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184932 (p : nat) (h1 : term0 p) : (term1 p) = (~ False).
Proof. exact (MK_COMB (@lem184931) (@lem184930 p h1)). Qed.
Lemma lem184934 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem184935 (p : nat) (h1 : term0 p) : (term1 p) = True.
Proof. exact (TRANS (@lem184932 p h1) (@lem184934)). Qed.
Lemma lem184936 (p : nat) (h1 : term0 p) : True = (term1 p).
Proof. exact (SYM (@lem184935 p h1)). Qed.
Lemma lem184937 (p : nat) (h1 : term0 p) : term1 p.
Proof. exact (EQ_MP (@lem184936 p h1) (@lem0)). Qed.
Lemma lem184938 (n : nat) (p : nat) (h1 : term0 p) : (term4 n p) = n.
Proof. exact (@lem184928 p n (@lem184937 p h1)). Qed.
Lemma lem184939 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem184940 (n : nat) (p : nat) (h1 : term0 p) : (n = (term4 n p)) = (n = n).
Proof. exact (MK_COMB (@lem184939 n) (@lem184938 n p h1)). Qed.
Lemma lem184942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem184943 (x : nat) : (x = x) = True.
Proof. exact (@lem184942 nat x). Qed.
Lemma lem184944 (n : nat) : (n = n) = True.
Proof. exact (@lem184943 n). Qed.
Lemma lem184945 (n : nat) (p : nat) (h1 : term0 p) : (n = (term4 n p)) = True.
Proof. exact (TRANS (@lem184940 n p h1) (@lem184944 n)). Qed.
Lemma lem184946 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term109 m n p) = (False \/ True).
Proof. exact (MK_COMB (@lem184923 m h1) (@lem184945 n p h2)). Qed.
Lemma lem184948 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem184949 : (False \/ True) = True.
Proof. exact (@lem184948 True). Qed.
Lemma lem184950 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term109 m n p) = True.
Proof. exact (TRANS (@lem184946 n m p h1 h2) (@lem184949)). Qed.
Lemma lem184951 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : True = (term109 m n p).
Proof. exact (SYM (@lem184950 n m p h1 h2)). Qed.
Lemma lem184952 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term109 m n p.
Proof. exact (EQ_MP (@lem184951 n m p h1 h2) (@lem0)). Qed.
Lemma lem184953 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (Nat.mul m n) = (term105 m n p).
Proof. exact (EQ_MP (@lem184869 m n p) (@lem184952 n m p h1 h2)). Qed.
Lemma lem184954 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (Nat.mul m n) = (term99 m n p).
Proof. exact (EQ_MP (@lem184851 m n p) (@lem184953 n m p h1 h2)). Qed.
Lemma lem184955 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term97 n m p.
Proof. exact (EQ_MP (@lem184839 n m p h1 h2) (@lem184954 n m p h1 h2)). Qed.
Lemma lem184956 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term115 n m p.
Proof. exact (ex_intro (term116 n m p) (term104 m n p) (@lem184955 n m p h1 h2)). Qed.
Lemma lem184958 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term77 n m p) = (Nat.div n p).
Proof. exact (@lem184561 m n p (@lem184956 n m p h1 h2)). Qed.
Lemma lem184959 (n : nat) (p : nat) (m : nat) (h1 : term0 m) : (term77 n m p) = (Nat.div n p).
Proof. exact (or_elim (@lem184406 p) (fun h0 : p = (NUMERAL 0) => @lem184491 m n p h0) (fun h0 : term0 p => @lem184958 n m p h1 h0)). Qed.
Lemma lem184960 (n : nat) (p : nat) (m : nat) (h1 : term0 m) : (term0 m) = ((term77 n m p) = (Nat.div n p)).
Proof. exact (prop_ext (fun h2 : term0 m => @lem184959 n p m h1) (fun h2 : (term77 n m p) = (Nat.div n p) => @lem184409 m h1)). Qed.
Lemma lem184961 (n : nat) (p : nat) (m : nat) (h1 : term0 m) : (term77 n m p) = (Nat.div n p).
Proof. exact (EQ_MP (@lem184960 n p m h1) (@lem184409 m h1)). Qed.
Lemma lem184962 (m : nat) (n : nat) (p : nat) : term117 m n p.
Proof. exact (fun h0 : term0 m => @lem184961 n p m h0). Qed.
Lemma lem184967 (m : nat) (n : nat) : term118 m n.
Proof. exact (fun p : nat => @lem184962 m n p). Qed.
Lemma lem184972 (m : nat) : term119 m.
Proof. exact (fun n : nat => @lem184967 m n). Qed.
Lemma lem184977 : term120.
Proof. exact (fun m : nat => @lem184972 m). Qed.
