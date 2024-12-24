Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm996664_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import BIT0_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import MULT_2_spec.
Require Import MULT_AC_spec.
Require Import MULT_ASSOC_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem996242 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem996243 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem996242 m n p h1)). Qed.
Lemma lem996244 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem996245 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem996244 m n p h1)). Qed.
Lemma lem996246 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem996243 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem996245 m n p h1)). Qed.
Lemma lem996247 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem996246 m n p)). Qed.
Lemma lem996248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem996249 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem996248) (@lem996247 m n)). Qed.
Lemma lem996250 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem996249 m n)). Qed.
Lemma lem996251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem996252 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem996251) (@lem996250 m)). Qed.
Lemma lem996253 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem996252 m)). Qed.
Lemma lem996254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem996255 : term12 = term13.
Proof. exact (MK_COMB (@lem996254) (@lem996253)). Qed.
Lemma lem996256 : term13.
Proof. exact (EQ_MP (@lem996255) (@lem82357)). Qed.
Lemma lem996257 : term14.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem996258 : term15.
Proof. exact (proj2 (@lem996257)). Qed.
Lemma lem996259 : term16.
Proof. exact (proj2 (@lem996258)). Qed.
Lemma lem996301 : term17.
Proof. exact (proj1 (@lem996259)). Qed.
Lemma lem996302 (n : nat) : term18 n.
Proof. exact (@lem996301 n). Qed.
Lemma lem996303 (n : nat) : (term18 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem996305 : term19.
Proof. exact (proj1 (@lem996258)). Qed.
Lemma lem996306 (n : nat) : term20 n.
Proof. exact (@lem996305 n). Qed.
Lemma lem996307 (n : nat) : (term20 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem996310 : term21.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem996311 (m : nat) : term22 m.
Proof. exact (@lem996310 m). Qed.
Lemma lem996312 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem996313 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem996312 m) (@lem996311 m)). Qed.
Lemma lem996314 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem996313 m n). Qed.
Lemma lem996315 (m : nat) (n : nat) : (term24 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem996317 (m : nat) : term25 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem996318 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem996319 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem996318 m) (@lem996317 m)). Qed.
Lemma lem996320 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem996319 m n). Qed.
Lemma lem996321 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem996322 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem996321 m n) (@lem996320 m n)). Qed.
Lemma lem996323 (m : nat) (n : nat) (p : nat) : term29 m n p.
Proof. exact (@lem996322 m n p). Qed.
Lemma lem996324 (m : nat) (n : nat) (p : nat) : (term29 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term30 m n p)).
Proof. exact (eq_refl (term29 m n p)). Qed.
Lemma lem996326 (m : nat) : term31 m.
Proof. exact (@lem996256 m). Qed.
Lemma lem996327 (m : nat) : (term31 m) = (term9 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem996328 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem996327 m) (@lem996326 m)). Qed.
Lemma lem996329 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem996328 m n). Qed.
Lemma lem996330 (m : nat) (n : nat) : (term32 m n) = (term5 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem996331 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem996330 m n) (@lem996329 m n)). Qed.
Lemma lem996332 (m : nat) (n : nat) (p : nat) : term33 m n p.
Proof. exact (@lem996331 m n p). Qed.
Lemma lem996333 (m : nat) (n : nat) (p : nat) : (term33 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem996335 {A : Type'} (x : A) : term34 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem996336 {A : Type'} (x : A) : (term34 A x) = ((x = x) = True).
Proof. exact (eq_refl (term34 A x)). Qed.
Lemma lem996338 (n : nat) (m : nat) (p : nat) : term35 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem996351 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem996352 (n : nat) : (term36 n) = (term37 n).
Proof. exact (@lem996351 n term38). Qed.
Lemma lem996356 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem996357 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem996356 m) (@lem996352 n)). Qed.
Lemma lem996364 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996365 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem996364) (@lem996357 m n)). Qed.
Lemma lem996367 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem996338 n m p)). Qed.
Lemma lem996368 (m : nat) (n : nat) : (term43 m n) = (term39 m n).
Proof. exact (@lem996367 m term38 n). Qed.
Lemma lem996376 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem996377 (n : nat) : (term36 n) = (term37 n).
Proof. exact (@lem996376 n term38). Qed.
Lemma lem996381 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem996382 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem996381 m) (@lem996377 n)). Qed.
Lemma lem996389 (m : nat) (n : nat) : (term43 m n) = (term40 m n).
Proof. exact (TRANS (@lem996368 m n) (@lem996382 m n)). Qed.
Lemma lem996390 (m : nat) (n : nat) : ((term39 m n) = (term43 m n)) = ((term40 m n) = (term40 m n)).
Proof. exact (MK_COMB (@lem996365 m n) (@lem996389 m n)). Qed.
Lemma lem996392 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem996336 A x) (@lem996335 A x)). Qed.
Lemma lem996393 (x : nat) : (x = x) = True.
Proof. exact (@lem996392 nat x). Qed.
Lemma lem996394 (m : nat) (n : nat) : ((term40 m n) = (term40 m n)) = True.
Proof. exact (@lem996393 (term40 m n)). Qed.
Lemma lem996395 (m : nat) (n : nat) : ((term39 m n) = (term43 m n)) = True.
Proof. exact (TRANS (@lem996390 m n) (@lem996394 m n)). Qed.
Lemma lem996396 (m : nat) (n : nat) : True = ((term39 m n) = (term43 m n)).
Proof. exact (SYM (@lem996395 m n)). Qed.
Lemma lem996399 (n : nat) (h1 : (term36 n) = (Nat.add n n)) : (term36 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem996400 (n : nat) (h1 : (term36 n) = (Nat.add n n)) : (Nat.add n n) = (term36 n).
Proof. exact (SYM (@lem996399 n h1)). Qed.
Lemma lem996401 (n : nat) (h1 : (Nat.add n n) = (term36 n)) : (Nat.add n n) = (term36 n).
Proof. exact (h1). Qed.
Lemma lem996402 (n : nat) (h1 : (Nat.add n n) = (term36 n)) : (term36 n) = (Nat.add n n).
Proof. exact (SYM (@lem996401 n h1)). Qed.
Lemma lem996403 (n : nat) : ((term36 n) = (Nat.add n n)) = ((Nat.add n n) = (term36 n)).
Proof. exact (prop_ext (fun h1 : (term36 n) = (Nat.add n n) => @lem996400 n h1) (fun h1 : (Nat.add n n) = (term36 n) => @lem996402 n h1)). Qed.
Lemma lem996404 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem996403 n)). Qed.
Lemma lem996405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem996406 : term46 = term47.
Proof. exact (MK_COMB (@lem996405) (@lem996404)). Qed.
Lemma lem996407 : term47.
Proof. exact (EQ_MP (@lem996406) (@lem84996)). Qed.
Lemma lem996408 (n : nat) : term48 n.
Proof. exact (@lem996407 n). Qed.
Lemma lem996409 (n : nat) : (term48 n) = ((Nat.add n n) = (term36 n)).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem996411 (n : nat) : term49 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem996412 (n : nat) : (term49 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem996423 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem996412 n) (@lem996411 n)). Qed.
Lemma lem996424 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem996423 m). Qed.
Lemma lem996425 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem996426 (m : nat) : (term50 m) = (term51 m).
Proof. exact (MK_COMB (@lem996425) (@lem996424 m)). Qed.
Lemma lem996427 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem996428 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem996426 m) (@lem996427 n)). Qed.
Lemma lem996429 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996430 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem996429) (@lem996428 m n)). Qed.
Lemma lem996432 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem996412 n) (@lem996411 n)). Qed.
Lemma lem996433 (p : nat) : (BIT0 p) = (Nat.add p p).
Proof. exact (@lem996432 p). Qed.
Lemma lem996434 (m : nat) (n : nat) (p : nat) : ((term52 m n) = (BIT0 p)) = ((term53 m n) = (Nat.add p p)).
Proof. exact (MK_COMB (@lem996430 m n) (@lem996433 p)). Qed.
Lemma lem996437 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996438 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term52 m n) = (BIT0 p))) = (((Nat.mul m n) = p) = ((term53 m n) = (Nat.add p p))).
Proof. exact (MK_COMB (@lem996437 m n p) (@lem996434 m n p)). Qed.
Lemma lem996441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem996442 (m : nat) (n : nat) (p : nat) : (term57 m n p) = (term58 m n p).
Proof. exact (MK_COMB (@lem996441) (@lem996438 m n p)). Qed.
Lemma lem996450 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem996412 n) (@lem996411 n)). Qed.
Lemma lem996451 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem996452 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem996451 m) (@lem996450 n)). Qed.
Lemma lem996453 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996454 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem996453) (@lem996452 m n)). Qed.
Lemma lem996456 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem996412 n) (@lem996411 n)). Qed.
Lemma lem996457 (p : nat) : (BIT0 p) = (Nat.add p p).
Proof. exact (@lem996456 p). Qed.
Lemma lem996458 (m : nat) (n : nat) (p : nat) : ((term59 m n) = (BIT0 p)) = ((term60 m n) = (Nat.add p p)).
Proof. exact (MK_COMB (@lem996454 m n) (@lem996457 p)). Qed.
Lemma lem996461 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996462 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term59 m n) = (BIT0 p))) = (((Nat.mul m n) = p) = ((term60 m n) = (Nat.add p p))).
Proof. exact (MK_COMB (@lem996461 m n p) (@lem996458 m n p)). Qed.
Lemma lem996465 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term64 m n p).
Proof. exact (MK_COMB (@lem996442 m n p) (@lem996462 m n p)). Qed.
Lemma lem996468 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term63 m n p).
Proof. exact (SYM (@lem996465 m n p)). Qed.
Lemma lem996478 (n : nat) : (Nat.add n n) = (term36 n).
Proof. exact (EQ_MP (@lem996409 n) (@lem996408 n)). Qed.
Lemma lem996479 (m : nat) : (Nat.add m m) = (term36 m).
Proof. exact (@lem996478 m). Qed.
Lemma lem996480 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem996481 (m : nat) : (term51 m) = (term65 m).
Proof. exact (MK_COMB (@lem996480) (@lem996479 m)). Qed.
Lemma lem996482 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem996483 (m : nat) (n : nat) : (term53 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem996481 m) (@lem996482 n)). Qed.
Lemma lem996484 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996485 (m : nat) (n : nat) : (term55 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem996484) (@lem996483 m n)). Qed.
Lemma lem996487 (n : nat) : (Nat.add n n) = (term36 n).
Proof. exact (EQ_MP (@lem996409 n) (@lem996408 n)). Qed.
Lemma lem996488 (p : nat) : (Nat.add p p) = (term36 p).
Proof. exact (@lem996487 p). Qed.
Lemma lem996489 (m : nat) (n : nat) (p : nat) : ((term53 m n) = (Nat.add p p)) = ((term66 m n) = (term36 p)).
Proof. exact (MK_COMB (@lem996485 m n) (@lem996488 p)). Qed.
Lemma lem996492 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996493 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term53 m n) = (Nat.add p p))) = (((Nat.mul m n) = p) = ((term66 m n) = (term36 p))).
Proof. exact (MK_COMB (@lem996492 m n p) (@lem996489 m n p)). Qed.
Lemma lem996496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem996497 (m : nat) (n : nat) (p : nat) : (term58 m n p) = (term68 m n p).
Proof. exact (MK_COMB (@lem996496) (@lem996493 m n p)). Qed.
Lemma lem996505 (n : nat) : (Nat.add n n) = (term36 n).
Proof. exact (EQ_MP (@lem996409 n) (@lem996408 n)). Qed.
Lemma lem996506 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem996507 (m : nat) (n : nat) : (term60 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem996506 m) (@lem996505 n)). Qed.
Lemma lem996508 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996509 (m : nat) (n : nat) : (term62 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem996508) (@lem996507 m n)). Qed.
Lemma lem996511 (n : nat) : (Nat.add n n) = (term36 n).
Proof. exact (EQ_MP (@lem996409 n) (@lem996408 n)). Qed.
Lemma lem996512 (p : nat) : (Nat.add p p) = (term36 p).
Proof. exact (@lem996511 p). Qed.
Lemma lem996513 (m : nat) (n : nat) (p : nat) : ((term60 m n) = (Nat.add p p)) = ((term39 m n) = (term36 p)).
Proof. exact (MK_COMB (@lem996509 m n) (@lem996512 p)). Qed.
Lemma lem996516 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996517 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term60 m n) = (Nat.add p p))) = (((Nat.mul m n) = p) = ((term39 m n) = (term36 p))).
Proof. exact (MK_COMB (@lem996516 m n p) (@lem996513 m n p)). Qed.
Lemma lem996520 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem996497 m n p) (@lem996517 m n p)). Qed.
Lemma lem996523 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term64 m n p).
Proof. exact (SYM (@lem996520 m n p)). Qed.
Lemma lem996539 (m : nat) (n : nat) : (term39 m n) = (term43 m n).
Proof. exact (EQ_MP (@lem996396 m n) (@lem0)). Qed.
Lemma lem996540 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996541 (m : nat) (n : nat) : (term41 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem996540) (@lem996539 m n)). Qed.
Lemma lem996542 (p : nat) : (term36 p) = (term36 p).
Proof. exact (eq_refl (term36 p)). Qed.
Lemma lem996543 (m : nat) (n : nat) (p : nat) : ((term39 m n) = (term36 p)) = ((term43 m n) = (term36 p)).
Proof. exact (MK_COMB (@lem996541 m n) (@lem996542 p)). Qed.
Lemma lem996546 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996547 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term39 m n) = (term36 p))) = (((Nat.mul m n) = p) = ((term43 m n) = (term36 p))).
Proof. exact (MK_COMB (@lem996546 m n p) (@lem996543 m n p)). Qed.
Lemma lem996550 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term68 m n p).
Proof. exact (eq_refl (term68 m n p)). Qed.
Lemma lem996551 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term71 m n p).
Proof. exact (MK_COMB (@lem996550 m n p) (@lem996547 m n p)). Qed.
Lemma lem996554 (m : nat) (n : nat) (p : nat) : (term71 m n p) = (term69 m n p).
Proof. exact (SYM (@lem996551 m n p)). Qed.
Lemma lem996566 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem996333 m n p) (@lem996332 m n p)). Qed.
Lemma lem996567 (m : nat) (n : nat) : (term66 m n) = (term43 m n).
Proof. exact (@lem996566 term38 m n). Qed.
Lemma lem996568 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem996569 (m : nat) (n : nat) : (term67 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem996568) (@lem996567 m n)). Qed.
Lemma lem996570 (p : nat) : (term36 p) = (term36 p).
Proof. exact (eq_refl (term36 p)). Qed.
Lemma lem996571 (m : nat) (n : nat) (p : nat) : ((term66 m n) = (term36 p)) = ((term43 m n) = (term36 p)).
Proof. exact (MK_COMB (@lem996569 m n) (@lem996570 p)). Qed.
Lemma lem996573 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term30 m n p).
Proof. exact (EQ_MP (@lem996324 m n p) (@lem996323 m n p)). Qed.
Lemma lem996574 (m : nat) (n : nat) (p : nat) : ((term43 m n) = (term36 p)) = (term72 m n p).
Proof. exact (@lem996573 term38 (Nat.mul m n) p). Qed.
Lemma lem996578 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem996315 m n) (@lem996314 m n)). Qed.
Lemma lem996579 : (term38 = (NUMERAL 0)) = (term73 = 0).
Proof. exact (@lem996578 term73 0). Qed.
Lemma lem996581 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem996307 n) (@lem996306 n)). Qed.
Lemma lem996582 : (term73 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem996581 (BIT1 0)). Qed.
Lemma lem996584 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem996303 n) (@lem996302 n)). Qed.
Lemma lem996585 : ((BIT1 0) = 0) = False.
Proof. exact (@lem996584 0). Qed.
Lemma lem996586 : (term73 = 0) = False.
Proof. exact (TRANS (@lem996582) (@lem996585)). Qed.
Lemma lem996587 : (term38 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem996579) (@lem996586)). Qed.
Lemma lem996588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem996589 : term74 = (or False).
Proof. exact (MK_COMB (@lem996588) (@lem996587)). Qed.
Lemma lem996592 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = p) = ((Nat.mul m n) = p).
Proof. exact (eq_refl ((Nat.mul m n) = p)). Qed.
Lemma lem996593 (m : nat) (n : nat) (p : nat) : (term72 m n p) = (term75 m n p).
Proof. exact (MK_COMB (@lem996589) (@lem996592 m n p)). Qed.
Lemma lem996595 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem996596 (m : nat) (n : nat) (p : nat) : (term75 m n p) = ((Nat.mul m n) = p).
Proof. exact (@lem996595 ((Nat.mul m n) = p)). Qed.
Lemma lem996599 (m : nat) (n : nat) (p : nat) : (term72 m n p) = ((Nat.mul m n) = p).
Proof. exact (TRANS (@lem996593 m n p) (@lem996596 m n p)). Qed.
Lemma lem996600 (m : nat) (n : nat) (p : nat) : ((term43 m n) = (term36 p)) = ((Nat.mul m n) = p).
Proof. exact (TRANS (@lem996574 m n p) (@lem996599 m n p)). Qed.
Lemma lem996601 (m : nat) (n : nat) (p : nat) : ((term66 m n) = (term36 p)) = ((Nat.mul m n) = p).
Proof. exact (TRANS (@lem996571 m n p) (@lem996600 m n p)). Qed.
Lemma lem996602 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996603 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term66 m n) = (term36 p))) = (((Nat.mul m n) = p) = ((Nat.mul m n) = p)).
Proof. exact (MK_COMB (@lem996602 m n p) (@lem996601 m n p)). Qed.
Lemma lem996605 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem996606 (x : Prop) : (x = x) = True.
Proof. exact (@lem996605 Prop x). Qed.
Lemma lem996607 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((Nat.mul m n) = p)) = True.
Proof. exact (@lem996606 ((Nat.mul m n) = p)). Qed.
Lemma lem996608 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term66 m n) = (term36 p))) = True.
Proof. exact (TRANS (@lem996603 m n p) (@lem996607 m n p)). Qed.
Lemma lem996609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem996610 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (and True).
Proof. exact (MK_COMB (@lem996609) (@lem996608 m n p)). Qed.
Lemma lem996616 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term30 m n p).
Proof. exact (EQ_MP (@lem996324 m n p) (@lem996323 m n p)). Qed.
Lemma lem996617 (m : nat) (n : nat) (p : nat) : ((term43 m n) = (term36 p)) = (term72 m n p).
Proof. exact (@lem996616 term38 (Nat.mul m n) p). Qed.
Lemma lem996621 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem996315 m n) (@lem996314 m n)). Qed.
Lemma lem996622 : (term38 = (NUMERAL 0)) = (term73 = 0).
Proof. exact (@lem996621 term73 0). Qed.
Lemma lem996624 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem996307 n) (@lem996306 n)). Qed.
Lemma lem996625 : (term73 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem996624 (BIT1 0)). Qed.
Lemma lem996627 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem996303 n) (@lem996302 n)). Qed.
Lemma lem996628 : ((BIT1 0) = 0) = False.
Proof. exact (@lem996627 0). Qed.
Lemma lem996629 : (term73 = 0) = False.
Proof. exact (TRANS (@lem996625) (@lem996628)). Qed.
Lemma lem996630 : (term38 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem996622) (@lem996629)). Qed.
Lemma lem996631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem996632 : term74 = (or False).
Proof. exact (MK_COMB (@lem996631) (@lem996630)). Qed.
Lemma lem996635 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = p) = ((Nat.mul m n) = p).
Proof. exact (eq_refl ((Nat.mul m n) = p)). Qed.
Lemma lem996636 (m : nat) (n : nat) (p : nat) : (term72 m n p) = (term75 m n p).
Proof. exact (MK_COMB (@lem996632) (@lem996635 m n p)). Qed.
Lemma lem996638 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem996639 (m : nat) (n : nat) (p : nat) : (term75 m n p) = ((Nat.mul m n) = p).
Proof. exact (@lem996638 ((Nat.mul m n) = p)). Qed.
Lemma lem996642 (m : nat) (n : nat) (p : nat) : (term72 m n p) = ((Nat.mul m n) = p).
Proof. exact (TRANS (@lem996636 m n p) (@lem996639 m n p)). Qed.
Lemma lem996643 (m : nat) (n : nat) (p : nat) : ((term43 m n) = (term36 p)) = ((Nat.mul m n) = p).
Proof. exact (TRANS (@lem996617 m n p) (@lem996642 m n p)). Qed.
Lemma lem996644 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term56 m n p).
Proof. exact (eq_refl (term56 m n p)). Qed.
Lemma lem996645 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term43 m n) = (term36 p))) = (((Nat.mul m n) = p) = ((Nat.mul m n) = p)).
Proof. exact (MK_COMB (@lem996644 m n p) (@lem996643 m n p)). Qed.
Lemma lem996647 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem996648 (x : Prop) : (x = x) = True.
Proof. exact (@lem996647 Prop x). Qed.
Lemma lem996649 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((Nat.mul m n) = p)) = True.
Proof. exact (@lem996648 ((Nat.mul m n) = p)). Qed.
Lemma lem996650 (m : nat) (n : nat) (p : nat) : (((Nat.mul m n) = p) = ((term43 m n) = (term36 p))) = True.
Proof. exact (TRANS (@lem996645 m n p) (@lem996649 m n p)). Qed.
Lemma lem996651 (m : nat) (n : nat) (p : nat) : (term71 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem996610 m n p) (@lem996650 m n p)). Qed.
Lemma lem996653 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem996654 : (True /\ True) = True.
Proof. exact (@lem996653 True). Qed.
Lemma lem996655 (m : nat) (n : nat) (p : nat) : (term71 m n p) = True.
Proof. exact (TRANS (@lem996651 m n p) (@lem996654)). Qed.
Lemma lem996656 (m : nat) (n : nat) (p : nat) : True = (term71 m n p).
Proof. exact (SYM (@lem996655 m n p)). Qed.
Lemma lem996657 (m : nat) (n : nat) (p : nat) : term71 m n p.
Proof. exact (EQ_MP (@lem996656 m n p) (@lem0)). Qed.
Lemma lem996658 (m : nat) (n : nat) (p : nat) : term69 m n p.
Proof. exact (EQ_MP (@lem996554 m n p) (@lem996657 m n p)). Qed.
Lemma lem996659 (m : nat) (n : nat) (p : nat) : term64 m n p.
Proof. exact (EQ_MP (@lem996523 m n p) (@lem996658 m n p)). Qed.
Lemma lem996662 (m : nat) (n : nat) (p : nat) : term63 m n p.
Proof. exact (EQ_MP (@lem996468 m n p) (@lem996659 m n p)). Qed.
Lemma lem996664 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = p) = ((term52 m n) = (BIT0 p)).
Proof. exact (proj1 (@lem996662 m n p)). Qed.
