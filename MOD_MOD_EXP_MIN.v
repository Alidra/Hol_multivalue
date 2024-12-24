Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MOD_EXP_MIN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXP_ADD_spec.
Require Import EXP_EQ_0_spec.
Require Import EXP_ZERO_spec.
Require Import LE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import LE_EXP_spec.
Require Import LTE_TRANS_spec.
Require Import MIN_spec.
Require Import MOD_0_spec.
Require Import MOD_1_spec.
Require Import MOD_LT_spec.
Require Import MOD_MOD_spec.
Require Import MOD_ZERO_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm1832_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem231357 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem231358 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem231357 h1 m). Qed.
Lemma lem231359 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem231360 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem231359 m) (@lem231358 m h1)). Qed.
Lemma lem231361 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem231360 m h1 n). Qed.
Lemma lem231362 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem231363 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem231362 n m) (@lem231361 m n h1)). Qed.
Lemma lem231364 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem231363 n m h1 p). Qed.
Lemma lem231365 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem231366 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem231365 n m p) (@lem231364 n m p h1)). Qed.
Lemma lem231367 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem231368 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.lt m p.
Proof. exact (@lem231366 n m p h1 (@lem231367 m n p h2)). Qed.
Lemma lem231369 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem231368 m n p h0 h1). Qed.
Lemma lem231370 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem231371 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem231370 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem231369 m n p h0)). Qed.
Lemma lem231372 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem231373 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.lt m p.
Proof. exact (@lem231371 m p h2 (@lem231372 h1)). Qed.
Lemma lem231374 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem231373 m p h1 h0). Qed.
Lemma lem231375 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem231374 m p h1). Qed.
Lemma lem231376 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem231375 m h1). Qed.
Lemma lem231377 : term14.
Proof. exact (fun h0 : term0 => @lem231376 h0). Qed.
Lemma lem231378 : term13.
Proof. exact (@lem231377 (@lem95941)). Qed.
Lemma lem231379 (m : nat) : term15 m.
Proof. exact (@lem231378 m). Qed.
Lemma lem231380 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem231381 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem231380 m) (@lem231379 m)). Qed.
Lemma lem231382 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem231381 m p). Qed.
Lemma lem231383 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem231385 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem231386 (m : nat) (h1 : term17) : term18 m.
Proof. exact (@lem231385 h1 m). Qed.
Lemma lem231387 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem231388 (m : nat) (h1 : term17) : term19 m.
Proof. exact (EQ_MP (@lem231387 m) (@lem231386 m h1)). Qed.
Lemma lem231389 (m : nat) (n : nat) (h1 : term17) : term20 m n.
Proof. exact (@lem231388 m h1 n). Qed.
Lemma lem231390 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem231391 (n : nat) (m : nat) (h1 : term17) : term21 n m.
Proof. exact (EQ_MP (@lem231390 n m) (@lem231389 m n h1)). Qed.
Lemma lem231392 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem231393 (m : nat) (n : nat) (h1 : term17) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem231391 n m h1 (@lem231392 m n h2)). Qed.
Lemma lem231394 (m : nat) (n : nat) (h1 : Peano.lt m n) : term22 n m.
Proof. exact (fun h0 : term17 => @lem231393 m n h0 h1). Qed.
Lemma lem231395 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem231396 (m : nat) (n : nat) (h1 : term17) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem231394 m n h2 (@lem231395 h1)). Qed.
Lemma lem231397 (n : nat) (m : nat) (h1 : term17) : term21 n m.
Proof. exact (fun h0 : Peano.lt m n => @lem231396 m n h1 h0). Qed.
Lemma lem231398 (n : nat) (h1 : term17) : term23 n.
Proof. exact (fun m : nat => @lem231397 n m h1). Qed.
Lemma lem231399 (h1 : term17) : term24.
Proof. exact (fun n : nat => @lem231398 n h1). Qed.
Lemma lem231400 : term25.
Proof. exact (fun h0 : term17 => @lem231399 h0). Qed.
Lemma lem231401 : term24.
Proof. exact (@lem231400 (@lem170673)). Qed.
Lemma lem231402 (n : nat) : term26 n.
Proof. exact (@lem231401 n). Qed.
Lemma lem231403 (n : nat) : (term26 n) = (term23 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem231404 (n : nat) : term23 n.
Proof. exact (EQ_MP (@lem231403 n) (@lem231402 n)). Qed.
Lemma lem231405 (n : nat) (m : nat) : term27 n m.
Proof. exact (@lem231404 n m). Qed.
Lemma lem231406 (n : nat) (m : nat) : (term27 n m) = (term21 n m).
Proof. exact (eq_refl (term27 n m)). Qed.
Lemma lem231408 (m : nat) : term28 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem231409 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem231410 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem231409 m) (@lem231408 m)). Qed.
Lemma lem231411 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem231410 m n). Qed.
Lemma lem231412 (n : nat) (m : nat) : (term30 m n) = ((Peano.le m n) = (term31 n m)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem231414 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem9784 (Peano.le m n)). Qed.
Lemma lem231415 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem231416 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem231415 m n) (@lem231414 m n)). Qed.
Lemma lem231417 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem231418 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem231419 (m : nat) : term35 m.
Proof. exact (@lem90961 m). Qed.
Lemma lem231420 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem231421 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem231420 m) (@lem231419 m)). Qed.
Lemma lem231422 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem231421 m n). Qed.
Lemma lem231423 (m : nat) (n : nat) : (term37 m n) = ((Nat.min m n) = (term38 m n)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem231435 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem9784 (Peano.le m n)). Qed.
Lemma lem231436 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem231437 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem231436 m n) (@lem231435 m n)). Qed.
Lemma lem231438 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem231439 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem231440 (m : nat) : term39 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem231441 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem231442 (m : nat) : term40 m.
Proof. exact (EQ_MP (@lem231441 m) (@lem231440 m)). Qed.
Lemma lem231444 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem231445 (p : nat) : term39 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem231446 (p : nat) : (term39 p) = (term40 p).
Proof. exact (eq_refl (term39 p)). Qed.
Lemma lem231447 (p : nat) : term40 p.
Proof. exact (EQ_MP (@lem231446 p) (@lem231445 p)). Qed.
Lemma lem231448 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231449 (p : nat) (h1 : term41 p) : term41 p.
Proof. exact (h1). Qed.
Lemma lem231450 (m : nat) : term35 m.
Proof. exact (@lem90961 m). Qed.
Lemma lem231451 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem231452 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem231451 m) (@lem231450 m)). Qed.
Lemma lem231453 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem231452 m n). Qed.
Lemma lem231454 (m : nat) (n : nat) : (term37 m n) = ((Nat.min m n) = (term38 m n)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem231456 (n : nat) : term42 n.
Proof. exact (@lem87446 n). Qed.
Lemma lem231457 (n : nat) : (term42 n) = ((term43 n) = (term44 n)).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem231462 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231463 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem231464 (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p) = term45.
Proof. exact (MK_COMB (@lem231463) (@lem231462 p h1)). Qed.
Lemma lem231465 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem231466 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p m) = (term43 m).
Proof. exact (MK_COMB (@lem231464 p h1) (@lem231465 m)). Qed.
Lemma lem231468 (n : nat) : (term43 n) = (term44 n).
Proof. exact (EQ_MP (@lem231457 n) (@lem231456 n)). Qed.
Lemma lem231469 (m : nat) : (term43 m) = (term44 m).
Proof. exact (@lem231468 m). Qed.
Lemma lem231474 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p m) = (term44 m).
Proof. exact (TRANS (@lem231466 m p h1) (@lem231469 m)). Qed.
Lemma lem231475 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231476 (x : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term46 x p m) = (term47 x m).
Proof. exact (MK_COMB (@lem231475 x) (@lem231474 m p h1)). Qed.
Lemma lem231477 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem231478 (x : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term48 x p m) = (term49 x m).
Proof. exact (MK_COMB (@lem231477) (@lem231476 x m p h1)). Qed.
Lemma lem231480 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231481 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem231482 (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p) = term45.
Proof. exact (MK_COMB (@lem231481) (@lem231480 p h1)). Qed.
Lemma lem231483 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem231484 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p n) = (term43 n).
Proof. exact (MK_COMB (@lem231482 p h1) (@lem231483 n)). Qed.
Lemma lem231486 (n : nat) : (term43 n) = (term44 n).
Proof. exact (EQ_MP (@lem231457 n) (@lem231456 n)). Qed.
Lemma lem231491 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p n) = (term44 n).
Proof. exact (TRANS (@lem231484 n p h1) (@lem231486 n)). Qed.
Lemma lem231492 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term50 x m p n) = (term51 x m n).
Proof. exact (MK_COMB (@lem231478 x m p h1) (@lem231491 n p h1)). Qed.
Lemma lem231493 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231494 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term52 x m p n) = (term53 x m n).
Proof. exact (MK_COMB (@lem231493) (@lem231492 x m n p h1)). Qed.
Lemma lem231496 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231497 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem231498 (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.pow p) = term45.
Proof. exact (MK_COMB (@lem231497) (@lem231496 p h1)). Qed.
Lemma lem231500 (m : nat) (n : nat) : (Nat.min m n) = (term38 m n).
Proof. exact (EQ_MP (@lem231454 m n) (@lem231453 m n)). Qed.
Lemma lem231501 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term54 p m n) = (term55 m n).
Proof. exact (MK_COMB (@lem231498 p h1) (@lem231500 m n)). Qed.
Lemma lem231503 (n : nat) : (term43 n) = (term44 n).
Proof. exact (EQ_MP (@lem231457 n) (@lem231456 n)). Qed.
Lemma lem231504 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (@lem231503 (term38 m n)). Qed.
Lemma lem231509 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term54 p m n) = (term56 m n).
Proof. exact (TRANS (@lem231501 m n p h1) (@lem231504 m n)). Qed.
Lemma lem231510 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231511 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term57 x p m n) = (term58 x m n).
Proof. exact (MK_COMB (@lem231510 x) (@lem231509 m n p h1)). Qed.
Lemma lem231512 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term50 x m p n) = (term57 x p m n)) = ((term51 x m n) = (term58 x m n)).
Proof. exact (MK_COMB (@lem231494 x m n p h1) (@lem231511 x m n p h1)). Qed.
Lemma lem231515 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term51 x m n) = (term58 x m n)) = ((term50 x m p n) = (term57 x p m n)).
Proof. exact (SYM (@lem231512 x m n p h1)). Qed.
Lemma lem231516 (n : nat) : term59 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem231517 (n : nat) : (term59 n) = (term60 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem231518 (n : nat) : term60 n.
Proof. exact (EQ_MP (@lem231517 n) (@lem231516 n)). Qed.
Lemma lem231519 (n : nat) : (term60 n) = ((term60 n) = True).
Proof. exact (@lem7 (term60 n)). Qed.
Lemma lem231521 (n : nat) : term61 n.
Proof. exact (@lem170050 n). Qed.
Lemma lem231522 (n : nat) : (term61 n) = ((term62 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem231524 (n : nat) : term63 n.
Proof. exact (@lem182042 n). Qed.
Lemma lem231525 (n : nat) : (term63 n) = ((term64 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term63 n)). Qed.
Lemma lem231537 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231538 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231539 (m : nat) (h1 : m = (NUMERAL 0)) : (@eq nat m) = term65.
Proof. exact (MK_COMB (@lem231538) (@lem231537 m h1)). Qed.
Lemma lem231540 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231541 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem231539 m h1) (@lem231540)). Qed.
Lemma lem231543 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231544 (x : nat) : (x = x) = True.
Proof. exact (@lem231543 nat x). Qed.
Lemma lem231545 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem231544 (NUMERAL 0)). Qed.
Lemma lem231546 (m : nat) (h1 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem231541 m h1) (@lem231545)). Qed.
Lemma lem231547 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231548 (m : nat) (h1 : m = (NUMERAL 0)) : (term66 m) = (@COND nat True).
Proof. exact (MK_COMB (@lem231547) (@lem231546 m h1)). Qed.
Lemma lem231549 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem231550 (m : nat) (h1 : m = (NUMERAL 0)) : (term68 m) = term69.
Proof. exact (MK_COMB (@lem231548 m h1) (@lem231549)). Qed.
Lemma lem231551 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231552 (m : nat) (h1 : m = (NUMERAL 0)) : (term44 m) = term70.
Proof. exact (MK_COMB (@lem231550 m h1) (@lem231551)). Qed.
Lemma lem231554 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem231555 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem231554 nat t2 t1). Qed.
Lemma lem231556 : term70 = term67.
Proof. exact (@lem231555 (NUMERAL 0) term67). Qed.
Lemma lem231557 (m : nat) (h1 : m = (NUMERAL 0)) : (term44 m) = term67.
Proof. exact (TRANS (@lem231552 m h1) (@lem231556)). Qed.
Lemma lem231558 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231559 (x : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term47 x m) = (term64 x).
Proof. exact (MK_COMB (@lem231558 x) (@lem231557 m h1)). Qed.
Lemma lem231561 (n : nat) : (term64 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem231525 n) (@lem231524 n)). Qed.
Lemma lem231562 (x : nat) : (term64 x) = (NUMERAL 0).
Proof. exact (@lem231561 x). Qed.
Lemma lem231563 (x : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term47 x m) = (NUMERAL 0).
Proof. exact (TRANS (@lem231559 x m h1) (@lem231562 x)). Qed.
Lemma lem231564 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem231565 (x : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term49 x m) = term71.
Proof. exact (MK_COMB (@lem231564) (@lem231563 x m h1)). Qed.
Lemma lem231570 (n : nat) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem231571 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term51 x m n) = (term72 n).
Proof. exact (MK_COMB (@lem231565 x m h1) (@lem231570 n)). Qed.
Lemma lem231573 (n : nat) : (term62 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem231522 n) (@lem231521 n)). Qed.
Lemma lem231574 (n : nat) : (term72 n) = (NUMERAL 0).
Proof. exact (@lem231573 (term44 n)). Qed.
Lemma lem231575 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term51 x m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem231571 x n m h1) (@lem231574 n)). Qed.
Lemma lem231576 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231577 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term53 x m n) = term65.
Proof. exact (MK_COMB (@lem231576) (@lem231575 x n m h1)). Qed.
Lemma lem231583 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231584 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem231585 (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m) = term73.
Proof. exact (MK_COMB (@lem231584) (@lem231583 m h1)). Qed.
Lemma lem231586 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem231587 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m n) = (term60 n).
Proof. exact (MK_COMB (@lem231585 m h1) (@lem231586 n)). Qed.
Lemma lem231589 (n : nat) : (term60 n) = True.
Proof. exact (EQ_MP (@lem231519 n) (@lem231518 n)). Qed.
Lemma lem231590 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le m n) = True.
Proof. exact (TRANS (@lem231587 n m h1) (@lem231589 n)). Qed.
Lemma lem231591 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231592 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term74 m n) = (@COND nat True).
Proof. exact (MK_COMB (@lem231591) (@lem231590 n m h1)). Qed.
Lemma lem231594 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231595 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term75 n m) = term76.
Proof. exact (MK_COMB (@lem231592 n m h1) (@lem231594 m h1)). Qed.
Lemma lem231596 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem231597 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term38 m n) = (term77 n).
Proof. exact (MK_COMB (@lem231595 n m h1) (@lem231596 n)). Qed.
Lemma lem231599 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem231600 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem231599 nat t2 t1). Qed.
Lemma lem231601 (n : nat) : (term77 n) = (NUMERAL 0).
Proof. exact (@lem231600 n (NUMERAL 0)). Qed.
Lemma lem231602 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term38 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem231597 n m h1) (@lem231601 n)). Qed.
Lemma lem231603 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231604 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term78 m n) = term65.
Proof. exact (MK_COMB (@lem231603) (@lem231602 n m h1)). Qed.
Lemma lem231605 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231606 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term38 m n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem231604 n m h1) (@lem231605)). Qed.
Lemma lem231608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231609 (x : nat) : (x = x) = True.
Proof. exact (@lem231608 nat x). Qed.
Lemma lem231610 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem231609 (NUMERAL 0)). Qed.
Lemma lem231611 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term38 m n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem231606 n m h1) (@lem231610)). Qed.
Lemma lem231612 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231613 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term79 m n) = (@COND nat True).
Proof. exact (MK_COMB (@lem231612) (@lem231611 n m h1)). Qed.
Lemma lem231614 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem231615 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term80 m n) = term69.
Proof. exact (MK_COMB (@lem231613 n m h1) (@lem231614)). Qed.
Lemma lem231616 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231617 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term56 m n) = term70.
Proof. exact (MK_COMB (@lem231615 n m h1) (@lem231616)). Qed.
Lemma lem231619 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem231620 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem231619 nat t2 t1). Qed.
Lemma lem231621 : term70 = term67.
Proof. exact (@lem231620 (NUMERAL 0) term67). Qed.
Lemma lem231622 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term56 m n) = term67.
Proof. exact (TRANS (@lem231617 n m h1) (@lem231621)). Qed.
Lemma lem231623 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231624 (n : nat) (x : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term58 x m n) = (term64 x).
Proof. exact (MK_COMB (@lem231623 x) (@lem231622 n m h1)). Qed.
Lemma lem231626 (n : nat) : (term64 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem231525 n) (@lem231524 n)). Qed.
Lemma lem231627 (x : nat) : (term64 x) = (NUMERAL 0).
Proof. exact (@lem231626 x). Qed.
Lemma lem231628 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term58 x m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem231624 n x m h1) (@lem231627 x)). Qed.
Lemma lem231629 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term51 x m n) = (term58 x m n)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem231577 x n m h1) (@lem231628 x n m h1)). Qed.
Lemma lem231631 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231632 (x : nat) : (x = x) = True.
Proof. exact (@lem231631 nat x). Qed.
Lemma lem231633 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem231632 (NUMERAL 0)). Qed.
Lemma lem231634 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term51 x m n) = (term58 x m n)) = True.
Proof. exact (TRANS (@lem231629 x n m h1) (@lem231633)). Qed.
Lemma lem231635 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : True = ((term51 x m n) = (term58 x m n)).
Proof. exact (SYM (@lem231634 x n m h1)). Qed.
Lemma lem231636 (x : nat) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term51 x m n) = (term58 x m n).
Proof. exact (EQ_MP (@lem231635 x n m h1) (@lem0)). Qed.
Lemma lem231648 (n : nat) : term81 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem231649 (n : nat) : (term81 n) = ((term82 n) = n).
Proof. exact (eq_refl (term81 n)). Qed.
Lemma lem231651 (m : nat) : term83 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem231669 (m : nat) (h1 : term41 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem231651 m (@lem231444 m h1)). Qed.
Lemma lem231670 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231671 (m : nat) (h1 : term41 m) : (term66 m) = (@COND nat False).
Proof. exact (MK_COMB (@lem231670) (@lem231669 m h1)). Qed.
Lemma lem231672 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem231673 (m : nat) (h1 : term41 m) : (term68 m) = term84.
Proof. exact (MK_COMB (@lem231671 m h1) (@lem231672)). Qed.
Lemma lem231674 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231675 (m : nat) (h1 : term41 m) : (term44 m) = term85.
Proof. exact (MK_COMB (@lem231673 m h1) (@lem231674)). Qed.
Lemma lem231677 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem231678 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem231677 nat t1 t2). Qed.
Lemma lem231679 : term85 = (NUMERAL 0).
Proof. exact (@lem231678 term67 (NUMERAL 0)). Qed.
Lemma lem231680 (m : nat) (h1 : term41 m) : (term44 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem231675 m h1) (@lem231679)). Qed.
Lemma lem231681 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231682 (x : nat) (m : nat) (h1 : term41 m) : (term47 x m) = (term82 x).
Proof. exact (MK_COMB (@lem231681 x) (@lem231680 m h1)). Qed.
Lemma lem231684 (n : nat) : (term82 n) = n.
Proof. exact (EQ_MP (@lem231649 n) (@lem231648 n)). Qed.
Lemma lem231685 (x : nat) : (term82 x) = x.
Proof. exact (@lem231684 x). Qed.
Lemma lem231686 (x : nat) (m : nat) (h1 : term41 m) : (term47 x m) = x.
Proof. exact (TRANS (@lem231682 x m h1) (@lem231685 x)). Qed.
Lemma lem231687 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem231688 (x : nat) (m : nat) (h1 : term41 m) : (term49 x m) = (Nat.modulo x).
Proof. exact (MK_COMB (@lem231687) (@lem231686 x m h1)). Qed.
Lemma lem231693 (n : nat) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem231694 (x : nat) (n : nat) (m : nat) (h1 : term41 m) : (term51 x m n) = (term47 x n).
Proof. exact (MK_COMB (@lem231688 x m h1) (@lem231693 n)). Qed.
Lemma lem231695 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231696 (x : nat) (n : nat) (m : nat) (h1 : term41 m) : (term53 x m n) = (term86 x n).
Proof. exact (MK_COMB (@lem231695) (@lem231694 x n m h1)). Qed.
Lemma lem231701 (x : nat) (m : nat) (n : nat) : (term58 x m n) = (term58 x m n).
Proof. exact (eq_refl (term58 x m n)). Qed.
Lemma lem231702 (x : nat) (n : nat) (m : nat) (h1 : term41 m) : ((term51 x m n) = (term58 x m n)) = ((term47 x n) = (term58 x m n)).
Proof. exact (MK_COMB (@lem231696 x n m h1) (@lem231701 x m n)). Qed.
Lemma lem231705 (x : nat) (n : nat) (m : nat) (h1 : term41 m) : ((term47 x n) = (term58 x m n)) = ((term51 x m n) = (term58 x m n)).
Proof. exact (SYM (@lem231702 x n m h1)). Qed.
Lemma lem231706 (m : nat) : term83 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem231719 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem231732 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem231719 m n) (@lem231438 m n h1)). Qed.
Lemma lem231733 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231734 (m : nat) (n : nat) (h1 : Peano.le m n) : (term74 m n) = (@COND nat True).
Proof. exact (MK_COMB (@lem231733) (@lem231732 m n h1)). Qed.
Lemma lem231735 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem231736 (m : nat) (n : nat) (h1 : Peano.le m n) : (term75 n m) = (@COND nat True m).
Proof. exact (MK_COMB (@lem231734 m n h1) (@lem231735 m)). Qed.
Lemma lem231737 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem231738 (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n) = (@COND nat True m n).
Proof. exact (MK_COMB (@lem231736 m n h1) (@lem231737 n)). Qed.
Lemma lem231740 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem231741 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem231740 nat t2 t1). Qed.
Lemma lem231742 (n : nat) (m : nat) : (@COND nat True m n) = m.
Proof. exact (@lem231741 n m). Qed.
Lemma lem231743 (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n) = m.
Proof. exact (TRANS (@lem231738 m n h1) (@lem231742 n m)). Qed.
Lemma lem231744 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231745 (m : nat) (n : nat) (h1 : Peano.le m n) : (term78 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem231744) (@lem231743 m n h1)). Qed.
Lemma lem231746 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231747 (m : nat) (n : nat) (h1 : Peano.le m n) : ((term38 m n) = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem231745 m n h1) (@lem231746)). Qed.
Lemma lem231749 (m : nat) (h1 : term41 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem231706 m (@lem231444 m h1)). Qed.
Lemma lem231750 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : ((term38 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem231747 m n h2) (@lem231749 m h1)). Qed.
Lemma lem231751 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231752 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : (term79 m n) = (@COND nat False).
Proof. exact (MK_COMB (@lem231751) (@lem231750 m n h1 h2)). Qed.
Lemma lem231753 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem231754 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : (term80 m n) = term84.
Proof. exact (MK_COMB (@lem231752 m n h1 h2) (@lem231753)). Qed.
Lemma lem231755 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231756 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : (term56 m n) = term85.
Proof. exact (MK_COMB (@lem231754 m n h1 h2) (@lem231755)). Qed.
Lemma lem231758 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem231759 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem231758 nat t1 t2). Qed.
Lemma lem231760 : term85 = (NUMERAL 0).
Proof. exact (@lem231759 term67 (NUMERAL 0)). Qed.
Lemma lem231761 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : (term56 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem231756 m n h1 h2) (@lem231760)). Qed.
Lemma lem231762 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231763 (x : nat) (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : (term58 x m n) = (term82 x).
Proof. exact (MK_COMB (@lem231762 x) (@lem231761 m n h1 h2)). Qed.
Lemma lem231764 (x : nat) (n : nat) : (term86 x n) = (term86 x n).
Proof. exact (eq_refl (term86 x n)). Qed.
Lemma lem231765 (x : nat) (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : ((term47 x n) = (term58 x m n)) = ((term47 x n) = (term82 x)).
Proof. exact (MK_COMB (@lem231764 x n) (@lem231763 x m n h1 h2)). Qed.
Lemma lem231768 (x : nat) (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : ((term47 x n) = (term82 x)) = ((term47 x n) = (term58 x m n)).
Proof. exact (SYM (@lem231765 x m n h1 h2)). Qed.
Lemma lem231782 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem231795 (m : nat) (n : nat) (h1 : term34 m n) : (Peano.le m n) = False.
Proof. exact (@lem231782 m n (@lem231439 m n h1)). Qed.
Lemma lem231796 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231797 (m : nat) (n : nat) (h1 : term34 m n) : (term74 m n) = (@COND nat False).
Proof. exact (MK_COMB (@lem231796) (@lem231795 m n h1)). Qed.
Lemma lem231798 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem231799 (m : nat) (n : nat) (h1 : term34 m n) : (term75 n m) = (@COND nat False m).
Proof. exact (MK_COMB (@lem231797 m n h1) (@lem231798 m)). Qed.
Lemma lem231800 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem231801 (m : nat) (n : nat) (h1 : term34 m n) : (term38 m n) = (@COND nat False m n).
Proof. exact (MK_COMB (@lem231799 m n h1) (@lem231800 n)). Qed.
Lemma lem231803 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem231804 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem231803 nat t1 t2). Qed.
Lemma lem231805 (m : nat) (n : nat) : (@COND nat False m n) = n.
Proof. exact (@lem231804 m n). Qed.
Lemma lem231806 (m : nat) (n : nat) (h1 : term34 m n) : (term38 m n) = n.
Proof. exact (TRANS (@lem231801 m n h1) (@lem231805 m n)). Qed.
Lemma lem231807 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231808 (m : nat) (n : nat) (h1 : term34 m n) : (term78 m n) = (@eq nat n).
Proof. exact (MK_COMB (@lem231807) (@lem231806 m n h1)). Qed.
Lemma lem231809 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231810 (m : nat) (n : nat) (h1 : term34 m n) : ((term38 m n) = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem231808 m n h1) (@lem231809)). Qed.
Lemma lem231813 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem231814 (m : nat) (n : nat) (h1 : term34 m n) : (term79 m n) = (term66 n).
Proof. exact (MK_COMB (@lem231813) (@lem231810 m n h1)). Qed.
Lemma lem231815 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem231816 (m : nat) (n : nat) (h1 : term34 m n) : (term80 m n) = (term68 n).
Proof. exact (MK_COMB (@lem231814 m n h1) (@lem231815)). Qed.
Lemma lem231817 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem231818 (m : nat) (n : nat) (h1 : term34 m n) : (term56 m n) = (term44 n).
Proof. exact (MK_COMB (@lem231816 m n h1) (@lem231817)). Qed.
Lemma lem231821 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem231822 (x : nat) (m : nat) (n : nat) (h1 : term34 m n) : (term58 x m n) = (term47 x n).
Proof. exact (MK_COMB (@lem231821 x) (@lem231818 m n h1)). Qed.
Lemma lem231823 (x : nat) (n : nat) : (term86 x n) = (term86 x n).
Proof. exact (eq_refl (term86 x n)). Qed.
Lemma lem231824 (x : nat) (m : nat) (n : nat) (h1 : term34 m n) : ((term47 x n) = (term58 x m n)) = ((term47 x n) = (term47 x n)).
Proof. exact (MK_COMB (@lem231823 x n) (@lem231822 x m n h1)). Qed.
Lemma lem231826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231827 (x : nat) : (x = x) = True.
Proof. exact (@lem231826 nat x). Qed.
Lemma lem231828 (x : nat) (n : nat) : ((term47 x n) = (term47 x n)) = True.
Proof. exact (@lem231827 (term47 x n)). Qed.
Lemma lem231829 (x : nat) (m : nat) (n : nat) (h1 : term34 m n) : ((term47 x n) = (term58 x m n)) = True.
Proof. exact (TRANS (@lem231824 x m n h1) (@lem231828 x n)). Qed.
Lemma lem231830 (x : nat) (m : nat) (n : nat) (h1 : term34 m n) : True = ((term47 x n) = (term58 x m n)).
Proof. exact (SYM (@lem231829 x m n h1)). Qed.
Lemma lem231831 (x : nat) (m : nat) (n : nat) (h1 : term34 m n) : (term47 x n) = (term58 x m n).
Proof. exact (EQ_MP (@lem231830 x m n h1) (@lem0)). Qed.
Lemma lem231832 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term88 _476 _475 _474 _477) = (term89 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem231833 (_474 : nat) (_475 : Prop) (x : nat) (_477 : nat) : (term90 x _475 _474 _477) = (term91 _474 _475 x _477).
Proof. exact (@lem231832 _474 _475 (term92 x) _477). Qed.
Lemma lem231834 (n : nat) (x : nat) : (term93 x n) = (term94 n x).
Proof. exact (@lem231833 term67 (n = (NUMERAL 0)) x (NUMERAL 0)). Qed.
Lemma lem231835 (x : nat) : (term95 x) = ((term82 x) = (term82 x)).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem231836 (n : nat) : (term96 n) = (term96 n).
Proof. exact (eq_refl (term96 n)). Qed.
Lemma lem231837 (n : nat) (x : nat) : (term97 n x) = (term98 n x).
Proof. exact (MK_COMB (@lem231836 n) (@lem231835 x)). Qed.
Lemma lem231838 (x : nat) : (term99 x) = ((term64 x) = (term82 x)).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem231839 (n : nat) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem231840 (n : nat) (x : nat) : (term101 n x) = (term102 n x).
Proof. exact (MK_COMB (@lem231839 n) (@lem231838 x)). Qed.
Lemma lem231841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem231842 (n : nat) (x : nat) : (term103 n x) = (term104 n x).
Proof. exact (MK_COMB (@lem231841) (@lem231840 n x)). Qed.
Lemma lem231843 (n : nat) (x : nat) : (term94 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem231842 n x) (@lem231837 n x)). Qed.
Lemma lem231844 (n : nat) (x : nat) : (term93 x n) = ((term47 x n) = (term82 x)).
Proof. exact (eq_refl (term93 x n)). Qed.
Lemma lem231845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem231846 (n : nat) (x : nat) : (term106 x n) = (term107 n x).
Proof. exact (MK_COMB (@lem231845) (@lem231844 n x)). Qed.
Lemma lem231847 (n : nat) (x : nat) : ((term93 x n) = (term94 n x)) = (((term47 x n) = (term82 x)) = (term105 n x)).
Proof. exact (MK_COMB (@lem231846 n x) (@lem231843 n x)). Qed.
Lemma lem231848 (n : nat) (x : nat) : ((term47 x n) = (term82 x)) = (term105 n x).
Proof. exact (EQ_MP (@lem231847 n x) (@lem231834 n x)). Qed.
Lemma lem231849 (n : nat) (x : nat) : (term105 n x) = ((term47 x n) = (term82 x)).
Proof. exact (SYM (@lem231848 n x)). Qed.
Lemma lem231850 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem231932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231933 (x : nat) : (x = x) = True.
Proof. exact (@lem231932 nat x). Qed.
Lemma lem231934 (x : nat) : ((term82 x) = (term82 x)) = True.
Proof. exact (@lem231933 (term82 x)). Qed.
Lemma lem231935 (x : nat) : True = ((term82 x) = (term82 x)).
Proof. exact (SYM (@lem231934 x)). Qed.
Lemma lem231938 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem231939 (x : nat) : ((term64 x) = (term82 x)) = (term109 x).
Proof. exact (@lem231938 ((term64 x) = (term82 x))). Qed.
Lemma lem231940 (x : nat) : (term109 x) = ((term64 x) = (term82 x)).
Proof. exact (SYM (@lem231939 x)). Qed.
Lemma lem231941 (x : nat) (h1 : term110 x) : term110 x.
Proof. exact (h1). Qed.
Lemma lem231944 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term111 p m n x) : term111 p m n x.
Proof. exact (h1). Qed.
Lemma lem231945 (p : nat) (m : nat) (n : nat) (x : nat) : term112 p m n x.
Proof. exact (fun h0 : term111 p m n x => @lem231944 p m n x h0). Qed.
Lemma lem231946 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term112 p m n x) : term112 p m n x.
Proof. exact (h1). Qed.
Lemma lem231947 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term111 p m n x) : term111 p m n x.
Proof. exact (h1). Qed.
Lemma lem231948 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term111 p m n x) (h2 : term112 p m n x) : term111 p m n x.
Proof. exact (@lem231946 p m n x h2 (@lem231947 p m n x h1)). Qed.
Lemma lem231949 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term111 p m n x) : term113 p m n x.
Proof. exact (fun h0 : term112 p m n x => @lem231948 p m n x h1 h0). Qed.
Lemma lem231950 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term112 p m n x) : term112 p m n x.
Proof. exact (h1). Qed.
Lemma lem231951 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term111 p m n x) (h2 : term112 p m n x) : term111 p m n x.
Proof. exact (@lem231949 p m n x h1 (@lem231950 p m n x h2)). Qed.
Lemma lem231952 (p : nat) (m : nat) (n : nat) (x : nat) (h1 : term112 p m n x) : term112 p m n x.
Proof. exact (fun h0 : term111 p m n x => @lem231951 p m n x h0 h1). Qed.
Lemma lem231953 (p : nat) (m : nat) (n : nat) (x : nat) : term114 p m n x.
Proof. exact (fun h0 : term112 p m n x => @lem231952 p m n x h0). Qed.
Lemma lem231956 (p : nat) (m : nat) (n : nat) (x : nat) : term112 p m n x.
Proof. exact (@lem231953 p m n x (@lem231945 p m n x)). Qed.
Lemma lem231984 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem231985 : term115 = term116.
Proof. exact (@lem231984 term117). Qed.
Lemma lem232002 (x : nat) : (term118 x) = (term118 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem232003 (x : nat) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem232002 x) (@lem231985)). Qed.
Lemma lem232006 (n : nat) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem232007 (n : nat) (x : nat) : (term121 n x) = (term122 n x).
Proof. exact (MK_COMB (@lem232006 n) (@lem232003 x)). Qed.
Lemma lem232010 (m : nat) (n : nat) : (term123 m n) = (term123 m n).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem232011 (m : nat) (n : nat) (x : nat) : (term124 m n x) = (term125 m n x).
Proof. exact (MK_COMB (@lem232010 m n) (@lem232007 n x)). Qed.
Lemma lem232014 (m : nat) : (term96 m) = (term96 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem232015 (m : nat) (n : nat) (x : nat) : (term126 m n x) = (term127 m n x).
Proof. exact (MK_COMB (@lem232014 m) (@lem232011 m n x)). Qed.
Lemma lem232018 (p : nat) : (term100 p) = (term100 p).
Proof. exact (eq_refl (term100 p)). Qed.
Lemma lem232019 (p : nat) (m : nat) (n : nat) (x : nat) : (term111 p m n x) = (term128 p m n x).
Proof. exact (MK_COMB (@lem232018 p) (@lem232015 m n x)). Qed.
Lemma lem232022 (m : nat) (n : nat) (x : nat) : (term129 m n x) = (term130 m n x).
Proof. exact (fun_ext (fun p : nat => @lem232019 p m n x)). Qed.
Lemma lem232023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232024 (m : nat) (n : nat) (x : nat) : (term131 m n x) = (term132 m n x).
Proof. exact (MK_COMB (@lem232023) (@lem232022 m n x)). Qed.
Lemma lem232029 (n : nat) (x : nat) : (term133 n x) = (term134 n x).
Proof. exact (fun_ext (fun m : nat => @lem232024 m n x)). Qed.
Lemma lem232030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232031 (n : nat) (x : nat) : (term135 n x) = (term136 n x).
Proof. exact (MK_COMB (@lem232030) (@lem232029 n x)). Qed.
Lemma lem232036 (x : nat) : (term137 x) = (term138 x).
Proof. exact (fun_ext (fun n : nat => @lem232031 n x)). Qed.
Lemma lem232037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232038 (x : nat) : (term139 x) = (term140 x).
Proof. exact (MK_COMB (@lem232037) (@lem232036 x)). Qed.
Lemma lem232043 : term141 = term142.
Proof. exact (fun_ext (fun x : nat => @lem232038 x)). Qed.
Lemma lem232044 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232053 : term143 = term144.
Proof. exact (MK_COMB (@lem232044) (@lem232043)). Qed.
Lemma lem232062 (m : nat) (n : nat) : ((term145 m n) = (term146 m n)) = ((term145 m n) = (term146 m n)).
Proof. exact (eq_refl ((term145 m n) = (term146 m n))). Qed.
Lemma lem232063 (m : nat) : (term147 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem232062 m n)). Qed.
Lemma lem232064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232065 (m : nat) : (term148 m) = (term148 m).
Proof. exact (MK_COMB (@lem232064) (@lem232063 m)). Qed.
Lemma lem232066 : term149 = term149.
Proof. exact (fun_ext (fun m : nat => @lem232065 m)). Qed.
Lemma lem232067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232068 : term150 = term150.
Proof. exact (MK_COMB (@lem232067) (@lem232066)). Qed.
Lemma lem232073 (m : nat) : ((term151 m) = (m = (NUMERAL 0))) = ((term151 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term151 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem232074 : term152 = term152.
Proof. exact (fun_ext (fun m : nat => @lem232073 m)). Qed.
Lemma lem232075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232076 : term153 = term153.
Proof. exact (MK_COMB (@lem232075) (@lem232074)). Qed.
Lemma lem232077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232078 : term154 = term154.
Proof. exact (MK_COMB (@lem232077) (@lem232076)). Qed.
Lemma lem232079 : term117 = term117.
Proof. exact (MK_COMB (@lem232078) (@lem232068)). Qed.
Lemma lem232080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem232081 : term116 = term116.
Proof. exact (MK_COMB (@lem232080) (@lem232079)). Qed.
Lemma lem232086 (x : nat) : (term118 x) = (term118 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem232087 (x : nat) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem232086 x) (@lem232081)). Qed.
Lemma lem232090 (n : nat) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem232091 (n : nat) (x : nat) : (term122 n x) = (term122 n x).
Proof. exact (MK_COMB (@lem232090 n) (@lem232087 x)). Qed.
Lemma lem232094 (m : nat) (n : nat) : (term123 m n) = (term123 m n).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem232095 (m : nat) (n : nat) (x : nat) : (term125 m n x) = (term125 m n x).
Proof. exact (MK_COMB (@lem232094 m n) (@lem232091 n x)). Qed.
Lemma lem232100 (m : nat) : (term96 m) = (term96 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem232101 (m : nat) (n : nat) (x : nat) : (term127 m n x) = (term127 m n x).
Proof. exact (MK_COMB (@lem232100 m) (@lem232095 m n x)). Qed.
Lemma lem232104 (p : nat) : (term100 p) = (term100 p).
Proof. exact (eq_refl (term100 p)). Qed.
Lemma lem232105 (p : nat) (m : nat) (n : nat) (x : nat) : (term128 p m n x) = (term128 p m n x).
Proof. exact (MK_COMB (@lem232104 p) (@lem232101 m n x)). Qed.
Lemma lem232106 (m : nat) (n : nat) (x : nat) : (term130 m n x) = (term130 m n x).
Proof. exact (fun_ext (fun p : nat => @lem232105 p m n x)). Qed.
Lemma lem232107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232108 (m : nat) (n : nat) (x : nat) : (term132 m n x) = (term132 m n x).
Proof. exact (MK_COMB (@lem232107) (@lem232106 m n x)). Qed.
Lemma lem232109 (n : nat) (x : nat) : (term134 n x) = (term134 n x).
Proof. exact (fun_ext (fun m : nat => @lem232108 m n x)). Qed.
Lemma lem232110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232111 (n : nat) (x : nat) : (term136 n x) = (term136 n x).
Proof. exact (MK_COMB (@lem232110) (@lem232109 n x)). Qed.
Lemma lem232112 (x : nat) : (term138 x) = (term138 x).
Proof. exact (fun_ext (fun n : nat => @lem232111 n x)). Qed.
Lemma lem232113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232114 (x : nat) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem232113) (@lem232112 x)). Qed.
Lemma lem232115 : term142 = term142.
Proof. exact (fun_ext (fun x : nat => @lem232114 x)). Qed.
Lemma lem232116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232117 : term144 = term144.
Proof. exact (MK_COMB (@lem232116) (@lem232115)). Qed.
Lemma lem232176 : term143 = term144.
Proof. exact (TRANS (@lem232053) (@lem232117)). Qed.
Lemma lem232177 : term144 = term143.
Proof. exact (SYM (@lem232176)). Qed.
Lemma lem232183 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem232195 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem232201 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem232207 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem232228 (m : nat) : ((term151 m) = (m = (NUMERAL 0))) = (term155 m).
Proof. exact (@lem17784 (term151 m) (m = (NUMERAL 0))). Qed.
Lemma lem232229 : term152 = term156.
Proof. exact (fun_ext (fun m : nat => @lem232228 m)). Qed.
Lemma lem232230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232231 : term153 = term157.
Proof. exact (MK_COMB (@lem232230) (@lem232229)). Qed.
Lemma lem232242 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (@lem17160 (m = (S n)) (Peano.le m n)). Qed.
Lemma lem232248 (m : nat) (n : nat) : (term160 m n) = (term160 m n).
Proof. exact (eq_refl (term160 m n)). Qed.
Lemma lem232250 (m : nat) (n : nat) : (term161 m n) = (term161 m n).
Proof. exact (eq_refl (term161 m n)). Qed.
Lemma lem232251 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (MK_COMB (@lem232250 m n) (@lem232242 m n)). Qed.
Lemma lem232252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232253 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem232252) (@lem232251 m n)). Qed.
Lemma lem232254 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (MK_COMB (@lem232253 m n) (@lem232248 m n)). Qed.
Lemma lem232255 (m : nat) (n : nat) : ((term145 m n) = (term146 m n)) = (term166 m n).
Proof. exact (@lem17784 (term145 m n) (term146 m n)). Qed.
Lemma lem232256 (m : nat) (n : nat) : ((term145 m n) = (term146 m n)) = (term167 m n).
Proof. exact (TRANS (@lem232255 m n) (@lem232254 m n)). Qed.
Lemma lem232257 (m : nat) : (term147 m) = (term168 m).
Proof. exact (fun_ext (fun n : nat => @lem232256 m n)). Qed.
Lemma lem232258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232259 (m : nat) : (term148 m) = (term169 m).
Proof. exact (MK_COMB (@lem232258) (@lem232257 m)). Qed.
Lemma lem232260 : term149 = term170.
Proof. exact (fun_ext (fun m : nat => @lem232259 m)). Qed.
Lemma lem232261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232262 : term150 = term171.
Proof. exact (MK_COMB (@lem232261) (@lem232260)). Qed.
Lemma lem232263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232264 : term154 = term172.
Proof. exact (MK_COMB (@lem232263) (@lem232231)). Qed.
Lemma lem232265 : term117 = term173.
Proof. exact (MK_COMB (@lem232264) (@lem232262)). Qed.
Lemma lem232267 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem232268 (P : nat -> Prop) (Q : nat -> Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem232267 nat P Q). Qed.
Lemma lem232269 : term178 = term179.
Proof. exact (@lem232268 term180 term181). Qed.
Lemma lem232270 (m : nat) : (term182 m) = (term183 m).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem232271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232272 (m : nat) : (term184 m) = (term185 m).
Proof. exact (MK_COMB (@lem232271) (@lem232270 m)). Qed.
Lemma lem232273 (m : nat) : (term186 m) = (term187 m).
Proof. exact (eq_refl (term186 m)). Qed.
Lemma lem232274 (m : nat) : (term188 m) = (term155 m).
Proof. exact (MK_COMB (@lem232272 m) (@lem232273 m)). Qed.
Lemma lem232275 : term189 = term156.
Proof. exact (fun_ext (fun m : nat => @lem232274 m)). Qed.
Lemma lem232276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232277 : term178 = term157.
Proof. exact (MK_COMB (@lem232276) (@lem232275)). Qed.
Lemma lem232278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem232279 : term190 = term191.
Proof. exact (MK_COMB (@lem232278) (@lem232277)). Qed.
Lemma lem232280 (m : nat) : (term182 m) = (term183 m).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem232281 : term192 = term180.
Proof. exact (fun_ext (fun m : nat => @lem232280 m)). Qed.
Lemma lem232282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232283 : term193 = term194.
Proof. exact (MK_COMB (@lem232282) (@lem232281)). Qed.
Lemma lem232284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232285 : term195 = term196.
Proof. exact (MK_COMB (@lem232284) (@lem232283)). Qed.
Lemma lem232286 (m : nat) : (term186 m) = (term187 m).
Proof. exact (eq_refl (term186 m)). Qed.
Lemma lem232287 : term197 = term181.
Proof. exact (fun_ext (fun m : nat => @lem232286 m)). Qed.
Lemma lem232288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232289 : term198 = term199.
Proof. exact (MK_COMB (@lem232288) (@lem232287)). Qed.
Lemma lem232290 : term179 = term200.
Proof. exact (MK_COMB (@lem232285) (@lem232289)). Qed.
Lemma lem232291 : (term178 = term179) = (term157 = term200).
Proof. exact (MK_COMB (@lem232279) (@lem232290)). Qed.
Lemma lem232292 : term157 = term200.
Proof. exact (EQ_MP (@lem232291) (@lem232269)). Qed.
Lemma lem232389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232390 : term172 = term201.
Proof. exact (MK_COMB (@lem232389) (@lem232292)). Qed.
Lemma lem232396 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem232397 (P : nat -> Prop) (Q : nat -> Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem232396 nat P Q). Qed.
Lemma lem232398 (m : nat) : (term202 m) = (term203 m).
Proof. exact (@lem232397 (term204 m) (term205 m)). Qed.
Lemma lem232399 (m : nat) (n : nat) : (term206 m n) = (term163 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem232400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232401 (m : nat) (n : nat) : (term207 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem232400) (@lem232399 m n)). Qed.
Lemma lem232402 (m : nat) (n : nat) : (term208 m n) = (term160 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem232403 (m : nat) (n : nat) : (term209 m n) = (term167 m n).
Proof. exact (MK_COMB (@lem232401 m n) (@lem232402 m n)). Qed.
Lemma lem232404 (m : nat) : (term210 m) = (term168 m).
Proof. exact (fun_ext (fun n : nat => @lem232403 m n)). Qed.
Lemma lem232405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232406 (m : nat) : (term202 m) = (term169 m).
Proof. exact (MK_COMB (@lem232405) (@lem232404 m)). Qed.
Lemma lem232407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem232408 (m : nat) : (term211 m) = (term212 m).
Proof. exact (MK_COMB (@lem232407) (@lem232406 m)). Qed.
Lemma lem232409 (m : nat) (n : nat) : (term206 m n) = (term163 m n).
Proof. exact (eq_refl (term206 m n)). Qed.
Lemma lem232410 (m : nat) : (term213 m) = (term204 m).
Proof. exact (fun_ext (fun n : nat => @lem232409 m n)). Qed.
Lemma lem232411 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232412 (m : nat) : (term214 m) = (term215 m).
Proof. exact (MK_COMB (@lem232411) (@lem232410 m)). Qed.
Lemma lem232413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232414 (m : nat) : (term216 m) = (term217 m).
Proof. exact (MK_COMB (@lem232413) (@lem232412 m)). Qed.
Lemma lem232415 (m : nat) (n : nat) : (term208 m n) = (term160 m n).
Proof. exact (eq_refl (term208 m n)). Qed.
Lemma lem232416 (m : nat) : (term218 m) = (term205 m).
Proof. exact (fun_ext (fun n : nat => @lem232415 m n)). Qed.
Lemma lem232417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232418 (m : nat) : (term219 m) = (term220 m).
Proof. exact (MK_COMB (@lem232417) (@lem232416 m)). Qed.
Lemma lem232419 (m : nat) : (term203 m) = (term221 m).
Proof. exact (MK_COMB (@lem232414 m) (@lem232418 m)). Qed.
Lemma lem232420 (m : nat) : ((term202 m) = (term203 m)) = ((term169 m) = (term221 m)).
Proof. exact (MK_COMB (@lem232408 m) (@lem232419 m)). Qed.
Lemma lem232421 (m : nat) : (term169 m) = (term221 m).
Proof. exact (EQ_MP (@lem232420 m) (@lem232398 m)). Qed.
Lemma lem232518 : term170 = term222.
Proof. exact (fun_ext (fun m : nat => @lem232421 m)). Qed.
Lemma lem232519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232520 : term171 = term223.
Proof. exact (MK_COMB (@lem232519) (@lem232518)). Qed.
Lemma lem232522 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem232523 (P : nat -> Prop) (Q : nat -> Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem232522 nat P Q). Qed.
Lemma lem232524 : term224 = term225.
Proof. exact (@lem232523 term226 term227). Qed.
Lemma lem232525 (m : nat) : (term228 m) = (term215 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem232526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232527 (m : nat) : (term229 m) = (term217 m).
Proof. exact (MK_COMB (@lem232526) (@lem232525 m)). Qed.
Lemma lem232528 (m : nat) : (term230 m) = (term220 m).
Proof. exact (eq_refl (term230 m)). Qed.
Lemma lem232529 (m : nat) : (term231 m) = (term221 m).
Proof. exact (MK_COMB (@lem232527 m) (@lem232528 m)). Qed.
Lemma lem232530 : term232 = term222.
Proof. exact (fun_ext (fun m : nat => @lem232529 m)). Qed.
Lemma lem232531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232532 : term224 = term223.
Proof. exact (MK_COMB (@lem232531) (@lem232530)). Qed.
Lemma lem232533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem232534 : term233 = term234.
Proof. exact (MK_COMB (@lem232533) (@lem232532)). Qed.
Lemma lem232535 (m : nat) : (term228 m) = (term215 m).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem232536 : term235 = term226.
Proof. exact (fun_ext (fun m : nat => @lem232535 m)). Qed.
Lemma lem232537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232538 : term236 = term237.
Proof. exact (MK_COMB (@lem232537) (@lem232536)). Qed.
Lemma lem232539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232540 : term238 = term239.
Proof. exact (MK_COMB (@lem232539) (@lem232538)). Qed.
Lemma lem232541 (m : nat) : (term230 m) = (term220 m).
Proof. exact (eq_refl (term230 m)). Qed.
Lemma lem232542 : term240 = term227.
Proof. exact (fun_ext (fun m : nat => @lem232541 m)). Qed.
Lemma lem232543 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232544 : term241 = term242.
Proof. exact (MK_COMB (@lem232543) (@lem232542)). Qed.
Lemma lem232545 : term225 = term243.
Proof. exact (MK_COMB (@lem232540) (@lem232544)). Qed.
Lemma lem232546 : (term224 = term225) = (term223 = term243).
Proof. exact (MK_COMB (@lem232534) (@lem232545)). Qed.
Lemma lem232547 : term223 = term243.
Proof. exact (EQ_MP (@lem232546) (@lem232524)). Qed.
Lemma lem232652 : term171 = term243.
Proof. exact (TRANS (@lem232520) (@lem232547)). Qed.
Lemma lem232655 : term173 = term244.
Proof. exact (MK_COMB (@lem232390) (@lem232652)). Qed.
Lemma lem232656 : term117 = term244.
Proof. exact (TRANS (@lem232265) (@lem232655)). Qed.
Lemma lem232657 (h1 : term117) : term244.
Proof. exact (EQ_MP (@lem232656) (@lem232183 h1)). Qed.
Lemma lem232675 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem232681 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem232689 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem232738 (m : nat) (n : nat) : (term160 m n) = (term160 m n).
Proof. exact (eq_refl (term160 m n)). Qed.
Lemma lem232739 (m : nat) : (term205 m) = (term205 m).
Proof. exact (fun_ext (fun n : nat => @lem232738 m n)). Qed.
Lemma lem232740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232741 (m : nat) : (term220 m) = (term220 m).
Proof. exact (MK_COMB (@lem232740) (@lem232739 m)). Qed.
Lemma lem232742 : term227 = term227.
Proof. exact (fun_ext (fun m : nat => @lem232741 m)). Qed.
Lemma lem232743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232744 : term242 = term242.
Proof. exact (MK_COMB (@lem232743) (@lem232742)). Qed.
Lemma lem232773 (m : nat) (n : nat) : (term163 m n) = (term163 m n).
Proof. exact (eq_refl (term163 m n)). Qed.
Lemma lem232774 (m : nat) : (term204 m) = (term204 m).
Proof. exact (fun_ext (fun n : nat => @lem232773 m n)). Qed.
Lemma lem232775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232776 (m : nat) : (term215 m) = (term215 m).
Proof. exact (MK_COMB (@lem232775) (@lem232774 m)). Qed.
Lemma lem232777 : term226 = term226.
Proof. exact (fun_ext (fun m : nat => @lem232776 m)). Qed.
Lemma lem232778 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232779 : term237 = term237.
Proof. exact (MK_COMB (@lem232778) (@lem232777)). Qed.
Lemma lem232780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232781 : term239 = term239.
Proof. exact (MK_COMB (@lem232780) (@lem232779)). Qed.
Lemma lem232782 : term243 = term243.
Proof. exact (MK_COMB (@lem232781) (@lem232744)). Qed.
Lemma lem232801 (m : nat) : (term187 m) = (term187 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem232802 : term181 = term181.
Proof. exact (fun_ext (fun m : nat => @lem232801 m)). Qed.
Lemma lem232803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232804 : term199 = term199.
Proof. exact (MK_COMB (@lem232803) (@lem232802)). Qed.
Lemma lem232823 (m : nat) : (term183 m) = (term183 m).
Proof. exact (eq_refl (term183 m)). Qed.
Lemma lem232824 : term180 = term180.
Proof. exact (fun_ext (fun m : nat => @lem232823 m)). Qed.
Lemma lem232825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232826 : term194 = term194.
Proof. exact (MK_COMB (@lem232825) (@lem232824)). Qed.
Lemma lem232827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232828 : term196 = term196.
Proof. exact (MK_COMB (@lem232827) (@lem232826)). Qed.
Lemma lem232829 : term200 = term200.
Proof. exact (MK_COMB (@lem232828) (@lem232804)). Qed.
Lemma lem232830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem232831 : term201 = term201.
Proof. exact (MK_COMB (@lem232830) (@lem232829)). Qed.
Lemma lem232832 : term244 = term244.
Proof. exact (MK_COMB (@lem232831) (@lem232782)). Qed.
Lemma lem232833 (h1 : term117) : term244.
Proof. exact (EQ_MP (@lem232832) (@lem232657 h1)). Qed.
Lemma lem232835 (h1 : term117) : term200.
Proof. exact (proj1 (@lem232833 h1)). Qed.
Lemma lem232838 (h1 : term117) : term199.
Proof. exact (proj2 (@lem232835 h1)). Qed.
Lemma lem232847 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem232851 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem232855 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem232928 (m : nat) : (term187 m) = (term187 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem232929 : term181 = term181.
Proof. exact (fun_ext (fun m : nat => @lem232928 m)). Qed.
Lemma lem232930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem232932 : term199 = term199.
Proof. exact (MK_COMB (@lem232930) (@lem232929)). Qed.
Lemma lem232933 (h1 : term117) : term199.
Proof. exact (EQ_MP (@lem232932) (@lem232838 h1)). Qed.
Lemma lem232949 (_4579 : nat) (h1 : term117) : term186 _4579.
Proof. exact (@lem232933 h1 _4579). Qed.
Lemma lem232950 (_4579 : nat) : (term186 _4579) = (term187 _4579).
Proof. exact (eq_refl (term186 _4579)). Qed.
Lemma lem232957 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem232959 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem232961 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem233039 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem233040 (m : nat) : (term245 m) = (term245 m).
Proof. exact (eq_refl (term245 m)). Qed.
Lemma lem233041 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term246 m n) = (term247 m).
Proof. exact (MK_COMB (@lem233040 m) (@lem232961 n h1)). Qed.
Lemma lem233042 (m : nat) : (term247 m) = (term151 m).
Proof. exact (eq_refl (term247 m)). Qed.
Lemma lem233043 (m : nat) (n : nat) : (term248 m n) = (term248 m n).
Proof. exact (eq_refl (term248 m n)). Qed.
Lemma lem233044 (n : nat) (m : nat) : ((term246 m n) = (term247 m)) = ((term246 m n) = (term151 m)).
Proof. exact (MK_COMB (@lem233043 m n) (@lem233042 m)). Qed.
Lemma lem233045 (m : nat) (n : nat) : (term246 m n) = (Peano.le m n).
Proof. exact (eq_refl (term246 m n)). Qed.
Lemma lem233046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem233047 (m : nat) (n : nat) : (term248 m n) = (term249 m n).
Proof. exact (MK_COMB (@lem233046) (@lem233045 m n)). Qed.
Lemma lem233048 (m : nat) : (term151 m) = (term151 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem233049 (n : nat) (m : nat) : ((term246 m n) = (term151 m)) = ((Peano.le m n) = (term151 m)).
Proof. exact (MK_COMB (@lem233047 m n) (@lem233048 m)). Qed.
Lemma lem233050 (n : nat) (m : nat) : ((term246 m n) = (term247 m)) = ((Peano.le m n) = (term151 m)).
Proof. exact (TRANS (@lem233044 n m) (@lem233049 n m)). Qed.
Lemma lem233051 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le m n) = (term151 m).
Proof. exact (EQ_MP (@lem233050 n m) (@lem233041 m n h1)). Qed.
Lemma lem233164 (m : nat) (h1 : term41 m) : term41 m.
Proof. exact (h1). Qed.
Lemma lem233234 (_4579 : nat) (h1 : term117) : term187 _4579.
Proof. exact (EQ_MP (@lem232950 _4579) (@lem232949 _4579 h1)). Qed.
Lemma lem233324 (m : nat) (n : nat) (h1 : Peano.le m n) (h2 : n = (NUMERAL 0)) : term151 m.
Proof. exact (EQ_MP (@lem233051 m n h2) (@lem232959 m n h1)). Qed.
Lemma lem233325 (m : nat) (n : nat) (h1 : Peano.le m n) (h2 : n = (NUMERAL 0)) : term250 m.
Proof. exact (fun h0 : term251 m => @lem233324 m n h1 h2). Qed.
Lemma lem233327 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem233328 (m : nat) : (term250 m) = (term151 m).
Proof. exact (@lem233327 (term151 m)). Qed.
Lemma lem233329 (m : nat) (n : nat) (h1 : Peano.le m n) (h2 : n = (NUMERAL 0)) : term151 m.
Proof. exact (EQ_MP (@lem233328 m) (@lem233325 m n h1 h2)). Qed.
Lemma lem233335 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem233336 (_4579 : nat) : (term187 _4579) = (term253 _4579).
Proof. exact (@lem233335 (_4579 = (NUMERAL 0)) (term251 _4579)). Qed.
Lemma lem233344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem233345 (_4579 : nat) : (term254 _4579) = (term255 _4579).
Proof. exact (MK_COMB (@lem233344) (@lem233336 _4579)). Qed.
Lemma lem233353 (_4579 : nat) : (term253 _4579) = (term253 _4579).
Proof. exact (eq_refl (term253 _4579)). Qed.
Lemma lem233354 (_4579 : nat) : ((term187 _4579) = (term253 _4579)) = ((term253 _4579) = (term253 _4579)).
Proof. exact (MK_COMB (@lem233345 _4579) (@lem233353 _4579)). Qed.
Lemma lem233356 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem233357 (x : Prop) : (x = x) = True.
Proof. exact (@lem233356 Prop x). Qed.
Lemma lem233358 (_4579 : nat) : ((term253 _4579) = (term253 _4579)) = True.
Proof. exact (@lem233357 (term253 _4579)). Qed.
Lemma lem233359 (_4579 : nat) : ((term187 _4579) = (term253 _4579)) = True.
Proof. exact (TRANS (@lem233354 _4579) (@lem233358 _4579)). Qed.
Lemma lem233360 (_4579 : nat) : True = ((term187 _4579) = (term253 _4579)).
Proof. exact (SYM (@lem233359 _4579)). Qed.
Lemma lem233361 (_4579 : nat) : (term187 _4579) = (term253 _4579).
Proof. exact (EQ_MP (@lem233360 _4579) (@lem0)). Qed.
Lemma lem233362 (_4579 : nat) (h1 : term117) : term253 _4579.
Proof. exact (EQ_MP (@lem233361 _4579) (@lem233234 _4579 h1)). Qed.
Lemma lem233364 (b : Prop) (a : Prop) : (a \/ b) = (term256 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem233365 (_4579 : nat) : (term253 _4579) = (term257 _4579).
Proof. exact (@lem233364 (term251 _4579) (_4579 = (NUMERAL 0))). Qed.
Lemma lem233367 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem233368 (_4579 : nat) : (term259 _4579) = (term151 _4579).
Proof. exact (@lem233367 (term151 _4579)). Qed.
Lemma lem233369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem233370 (_4579 : nat) : (term260 _4579) = (term261 _4579).
Proof. exact (MK_COMB (@lem233369) (@lem233368 _4579)). Qed.
Lemma lem233371 (_4579 : nat) : (_4579 = (NUMERAL 0)) = (_4579 = (NUMERAL 0)).
Proof. exact (eq_refl (_4579 = (NUMERAL 0))). Qed.
Lemma lem233372 (_4579 : nat) : (term257 _4579) = (term262 _4579).
Proof. exact (MK_COMB (@lem233370 _4579) (@lem233371 _4579)). Qed.
Lemma lem233373 (_4579 : nat) : (term253 _4579) = (term262 _4579).
Proof. exact (TRANS (@lem233365 _4579) (@lem233372 _4579)). Qed.
Lemma lem233376 (_4579 : nat) (h1 : term117) : term262 _4579.
Proof. exact (EQ_MP (@lem233373 _4579) (@lem233362 _4579 h1)). Qed.
Lemma lem233377 (m : nat) (h1 : term117) : term262 m.
Proof. exact (@lem233376 m h1). Qed.
Lemma lem233380 (m : nat) (n : nat) (h1 : term117) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (@lem233377 m h1 (@lem233329 m n h2 h3)). Qed.
Lemma lem233381 (m : nat) (n : nat) (h1 : term117) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : term263 m.
Proof. exact (fun h0 : term41 m => @lem233380 m n h1 h2 h3). Qed.
Lemma lem233383 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem233384 (m : nat) : (term263 m) = (m = (NUMERAL 0)).
Proof. exact (@lem233383 (m = (NUMERAL 0))). Qed.
Lemma lem233385 (m : nat) (n : nat) (h1 : term117) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (EQ_MP (@lem233384 m) (@lem233381 m n h1 h2 h3)). Qed.
Lemma lem233388 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem233390 (m : nat) : (term41 m) = (term264 m).
Proof. exact (@lem233388 (m = (NUMERAL 0))). Qed.
Lemma lem233393 (m : nat) (h1 : term41 m) : term264 m.
Proof. exact (EQ_MP (@lem233390 m) (@lem233164 m h1)). Qed.
Lemma lem233396 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (@lem233393 m h1 (@lem233385 m n h2 h3 h4)). Qed.
Lemma lem233397 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : term265.
Proof. exact (fun h0 : ~ False => @lem233396 m n h1 h2 h3 h4). Qed.
Lemma lem233399 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem233400 : term265 = False.
Proof. exact (@lem233399 False). Qed.
Lemma lem233401 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233400) (@lem233397 m n h1 h2 h3 h4)). Qed.
Lemma lem233402 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233401 m n h1 h2 h3 h4) (fun h5 : False => @lem233164 m h1)). Qed.
Lemma lem233404 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233402 m n h1 h2 h3 h4) (@lem233164 m h1)). Qed.
Lemma lem233405 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233404 m n h1 h2 h3 h4) (fun h5 : False => @lem233039 m h1)). Qed.
Lemma lem233407 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233405 m n h1 h2 h3 h4) (@lem233039 m h1)). Qed.
Lemma lem233408 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233407 m n h1 h2 h3 h4) (fun h5 : False => @lem232961 n h4)). Qed.
Lemma lem233409 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233408 m n h1 h2 h3 h4) (@lem232961 n h4)). Qed.
Lemma lem233410 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem233409 m n h1 h2 h3 h4) (fun h5 : False => @lem232959 m n h3)). Qed.
Lemma lem233411 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233410 m n h1 h2 h3 h4) (@lem232959 m n h3)). Qed.
Lemma lem233412 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233411 m n h1 h2 h3 h4) (fun h5 : False => @lem232957 m h1)). Qed.
Lemma lem233413 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233412 m n h1 h2 h3 h4) (@lem232957 m h1)). Qed.
Lemma lem233414 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233413 m n h1 h2 h3 h4) (fun h5 : False => @lem232855 n h4)). Qed.
Lemma lem233415 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233414 m n h1 h2 h3 h4) (@lem232855 n h4)). Qed.
Lemma lem233416 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem233415 m n h1 h2 h3 h4) (fun h5 : False => @lem232851 m n h3)). Qed.
Lemma lem233417 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233416 m n h1 h2 h3 h4) (@lem232851 m n h3)). Qed.
Lemma lem233418 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233417 m n h1 h2 h3 h4) (fun h5 : False => @lem232847 m h1)). Qed.
Lemma lem233419 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233418 m n h1 h2 h3 h4) (@lem232847 m h1)). Qed.
Lemma lem233420 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233419 m n h1 h2 h3 h4) (fun h5 : False => @lem232855 n h4)). Qed.
Lemma lem233421 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233420 m n h1 h2 h3 h4) (@lem232855 n h4)). Qed.
Lemma lem233422 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem233421 m n h1 h2 h3 h4) (fun h5 : False => @lem232851 m n h3)). Qed.
Lemma lem233423 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233422 m n h1 h2 h3 h4) (@lem232851 m n h3)). Qed.
Lemma lem233424 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233423 m n h1 h2 h3 h4) (fun h5 : False => @lem232847 m h1)). Qed.
Lemma lem233425 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233424 m n h1 h2 h3 h4) (@lem232847 m h1)). Qed.
Lemma lem233426 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233425 m n h1 h2 h3 h4) (fun h5 : False => @lem232689 n h4)). Qed.
Lemma lem233427 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233426 m n h1 h2 h3 h4) (@lem232689 n h4)). Qed.
Lemma lem233428 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem233427 m n h1 h2 h3 h4) (fun h5 : False => @lem232681 m n h3)). Qed.
Lemma lem233429 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233428 m n h1 h2 h3 h4) (@lem232681 m n h3)). Qed.
Lemma lem233430 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233429 m n h1 h2 h3 h4) (fun h5 : False => @lem232675 m h1)). Qed.
Lemma lem233431 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233430 m n h1 h2 h3 h4) (@lem232675 m h1)). Qed.
Lemma lem233432 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233431 m n h1 h2 h3 h4) (fun h5 : False => @lem232207 n h4)). Qed.
Lemma lem233433 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233432 m n h1 h2 h3 h4) (@lem232207 n h4)). Qed.
Lemma lem233434 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem233433 m n h1 h2 h3 h4) (fun h5 : False => @lem232201 m n h3)). Qed.
Lemma lem233435 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233434 m n h1 h2 h3 h4) (@lem232201 m n h3)). Qed.
Lemma lem233436 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : (term41 m) = False.
Proof. exact (prop_ext (fun h5 : term41 m => @lem233435 m n h1 h2 h3 h4) (fun h5 : False => @lem232195 m h1)). Qed.
Lemma lem233437 (m : nat) (n : nat) (h1 : term41 m) (h2 : term117) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233436 m n h1 h2 h3 h4) (@lem232195 m h1)). Qed.
Lemma lem233438 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : term115.
Proof. exact (fun h0 : term117 => @lem233437 m n h1 h0 h2 h3). Qed.
Lemma lem233439 : term115 = term116.
Proof. exact (@lem69 term117). Qed.
Lemma lem233440 (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : term116.
Proof. exact (EQ_MP (@lem233439) (@lem233438 m n h1 h2 h3)). Qed.
Lemma lem233441 (x : nat) (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) : term120 x.
Proof. exact (fun h0 : term110 x => @lem233440 m n h1 h2 h3). Qed.
Lemma lem233442 (x : nat) (m : nat) (n : nat) (h1 : term41 m) (h2 : Peano.le m n) : term122 n x.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem233441 x m n h1 h2 h0). Qed.
Lemma lem233443 (n : nat) (x : nat) (m : nat) (h1 : term41 m) : term125 m n x.
Proof. exact (fun h0 : Peano.le m n => @lem233442 x m n h1 h0). Qed.
Lemma lem233444 (m : nat) (n : nat) (x : nat) : term127 m n x.
Proof. exact (fun h0 : term41 m => @lem233443 n x m h0). Qed.
Lemma lem233445 (p : nat) (m : nat) (n : nat) (x : nat) : term128 p m n x.
Proof. exact (fun h0 : p = (NUMERAL 0) => @lem233444 m n x). Qed.
Lemma lem233450 (m : nat) (n : nat) (x : nat) : term132 m n x.
Proof. exact (fun p : nat => @lem233445 p m n x). Qed.
Lemma lem233455 (n : nat) (x : nat) : term136 n x.
Proof. exact (fun m : nat => @lem233450 m n x). Qed.
Lemma lem233460 (x : nat) : term140 x.
Proof. exact (fun n : nat => @lem233455 n x). Qed.
Lemma lem233465 : term144.
Proof. exact (fun x : nat => @lem233460 x). Qed.
Lemma lem233466 : term143.
Proof. exact (EQ_MP (@lem232177) (@lem233465)). Qed.
Lemma lem233467 (x : nat) : term266 x.
Proof. exact (@lem233466 x). Qed.
Lemma lem233468 (x : nat) : (term266 x) = (term139 x).
Proof. exact (eq_refl (term266 x)). Qed.
Lemma lem233469 (x : nat) : term139 x.
Proof. exact (EQ_MP (@lem233468 x) (@lem233467 x)). Qed.
Lemma lem233470 (x : nat) (n : nat) : term267 x n.
Proof. exact (@lem233469 x n). Qed.
Lemma lem233471 (n : nat) (x : nat) : (term267 x n) = (term135 n x).
Proof. exact (eq_refl (term267 x n)). Qed.
Lemma lem233472 (n : nat) (x : nat) : term135 n x.
Proof. exact (EQ_MP (@lem233471 n x) (@lem233470 x n)). Qed.
Lemma lem233473 (n : nat) (x : nat) (m : nat) : term268 n x m.
Proof. exact (@lem233472 n x m). Qed.
Lemma lem233474 (m : nat) (n : nat) (x : nat) : (term268 n x m) = (term131 m n x).
Proof. exact (eq_refl (term268 n x m)). Qed.
Lemma lem233475 (m : nat) (n : nat) (x : nat) : term131 m n x.
Proof. exact (EQ_MP (@lem233474 m n x) (@lem233473 n x m)). Qed.
Lemma lem233476 (m : nat) (n : nat) (x : nat) (p : nat) : term269 m n x p.
Proof. exact (@lem233475 m n x p). Qed.
Lemma lem233477 (p : nat) (m : nat) (n : nat) (x : nat) : (term269 m n x p) = (term111 p m n x).
Proof. exact (eq_refl (term269 m n x p)). Qed.
Lemma lem233478 (p : nat) (m : nat) (n : nat) (x : nat) : term111 p m n x.
Proof. exact (EQ_MP (@lem233477 p m n x) (@lem233476 m n x p)). Qed.
Lemma lem233480 (p : nat) (m : nat) (n : nat) (x : nat) : term111 p m n x.
Proof. exact (@lem231956 p m n x (@lem233478 p m n x)). Qed.
Lemma lem233481 (m : nat) (n : nat) (x : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term126 m n x.
Proof. exact (@lem233480 p m n x (@lem231448 p h1)). Qed.
Lemma lem233482 (n : nat) (x : nat) (m : nat) (p : nat) (h1 : term41 m) (h2 : p = (NUMERAL 0)) : term124 m n x.
Proof. exact (@lem233481 m n x p h2 (@lem231444 m h1)). Qed.
Lemma lem233483 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : p = (NUMERAL 0)) : term121 n x.
Proof. exact (@lem233482 n x m p h1 h3 (@lem231438 m n h2)). Qed.
Lemma lem233484 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) (h4 : p = (NUMERAL 0)) : term119 x.
Proof. exact (@lem233483 x m n p h1 h2 h4 (@lem231850 n h3)). Qed.
Lemma lem233485 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : term110 x) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) (h5 : p = (NUMERAL 0)) : term115.
Proof. exact (@lem233484 x m n p h1 h3 h4 h5 (@lem231941 x h2)). Qed.
Lemma lem233486 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : term110 x) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (@lem233485 x m n p h1 h2 h3 h4 h5 (@lem89501)). Qed.
Lemma lem233487 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : term110 x) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) (h5 : p = (NUMERAL 0)) : (term110 x) = False.
Proof. exact (prop_ext (fun h6 : term110 x => @lem233486 x m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem231941 x h2)). Qed.
Lemma lem233488 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : term110 x) (h3 : Peano.le m n) (h4 : n = (NUMERAL 0)) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem233487 x m n p h1 h2 h3 h4 h5) (@lem231941 x h2)). Qed.
Lemma lem233489 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) (h4 : p = (NUMERAL 0)) : term109 x.
Proof. exact (fun h0 : term110 x => @lem233488 x m n p h1 h0 h2 h3 h4). Qed.
Lemma lem233492 (x : nat) : (term82 x) = (term82 x).
Proof. exact (EQ_MP (@lem231935 x) (@lem0)). Qed.
Lemma lem233493 (n : nat) (x : nat) : term98 n x.
Proof. exact (fun h0 : term41 n => @lem233492 x). Qed.
Lemma lem233494 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) (h4 : p = (NUMERAL 0)) : (term64 x) = (term82 x).
Proof. exact (EQ_MP (@lem231940 x) (@lem233489 x m n p h1 h2 h3 h4)). Qed.
Lemma lem233495 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) (h4 : p = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((term64 x) = (term82 x)).
Proof. exact (prop_ext (fun h5 : n = (NUMERAL 0) => @lem233494 x m n p h1 h2 h3 h4) (fun h5 : (term64 x) = (term82 x) => @lem231850 n h3)). Qed.
Lemma lem233496 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : n = (NUMERAL 0)) (h4 : p = (NUMERAL 0)) : (term64 x) = (term82 x).
Proof. exact (EQ_MP (@lem233495 x m n p h1 h2 h3 h4) (@lem231850 n h3)). Qed.
Lemma lem233497 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : p = (NUMERAL 0)) : term102 n x.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem233496 x m n p h1 h2 h0 h3). Qed.
Lemma lem233498 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : p = (NUMERAL 0)) : term105 n x.
Proof. exact (conj (@lem233497 x m n p h1 h2 h3) (@lem233493 n x)). Qed.
Lemma lem233499 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : p = (NUMERAL 0)) : (term47 x n) = (term82 x).
Proof. exact (EQ_MP (@lem231849 n x) (@lem233498 x m n p h1 h2 h3)). Qed.
Lemma lem233500 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 m) (h2 : Peano.le m n) (h3 : p = (NUMERAL 0)) : (term47 x n) = (term58 x m n).
Proof. exact (EQ_MP (@lem231768 x m n h1 h2) (@lem233499 x m n p h1 h2 h3)). Qed.
Lemma lem233501 (x : nat) (n : nat) (m : nat) (p : nat) (h1 : term41 m) (h2 : p = (NUMERAL 0)) : (term47 x n) = (term58 x m n).
Proof. exact (or_elim (@lem231437 m n) (fun h0 : Peano.le m n => @lem233500 x m n p h1 h0 h2) (fun h0 : term34 m n => @lem231831 x m n h0)). Qed.
Lemma lem233502 (x : nat) (n : nat) (m : nat) (p : nat) (h1 : term41 m) (h2 : p = (NUMERAL 0)) : (term51 x m n) = (term58 x m n).
Proof. exact (EQ_MP (@lem231705 x n m h1) (@lem233501 x n m p h1 h2)). Qed.
Lemma lem233503 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term51 x m n) = (term58 x m n).
Proof. exact (or_elim (@lem231442 m) (fun h0 : m = (NUMERAL 0) => @lem231636 x n m h0) (fun h0 : term41 m => @lem233502 x n m p h0 h1)). Qed.
Lemma lem233504 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term50 x m p n) = (term57 x p m n).
Proof. exact (EQ_MP (@lem231515 x m n p h1) (@lem233503 x m n p h1)). Qed.
Lemma lem233508 (m : nat) (n : nat) : (Nat.min m n) = (term38 m n).
Proof. exact (EQ_MP (@lem231423 m n) (@lem231422 m n)). Qed.
Lemma lem233509 (p : nat) : (Nat.pow p) = (Nat.pow p).
Proof. exact (eq_refl (Nat.pow p)). Qed.
Lemma lem233510 (p : nat) (m : nat) (n : nat) : (term54 p m n) = (term270 p m n).
Proof. exact (MK_COMB (@lem233509 p) (@lem233508 m n)). Qed.
Lemma lem233511 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem233512 (x : nat) (p : nat) (m : nat) (n : nat) : (term57 x p m n) = (term271 x p m n).
Proof. exact (MK_COMB (@lem233511 x) (@lem233510 p m n)). Qed.
Lemma lem233513 (x : nat) (m : nat) (p : nat) (n : nat) : (term52 x m p n) = (term52 x m p n).
Proof. exact (eq_refl (term52 x m p n)). Qed.
Lemma lem233514 (x : nat) (p : nat) (m : nat) (n : nat) : ((term50 x m p n) = (term57 x p m n)) = ((term50 x m p n) = (term271 x p m n)).
Proof. exact (MK_COMB (@lem233513 x m p n) (@lem233512 x p m n)). Qed.
Lemma lem233517 (x : nat) (p : nat) (m : nat) (n : nat) : ((term50 x m p n) = (term271 x p m n)) = ((term50 x m p n) = (term57 x p m n)).
Proof. exact (SYM (@lem233514 x p m n)). Qed.
Lemma lem233531 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem233536 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem233531 m n) (@lem231417 m n h1)). Qed.
Lemma lem233537 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem233538 (m : nat) (n : nat) (h1 : Peano.le m n) : (term74 m n) = (@COND nat True).
Proof. exact (MK_COMB (@lem233537) (@lem233536 m n h1)). Qed.
Lemma lem233539 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem233540 (m : nat) (n : nat) (h1 : Peano.le m n) : (term75 n m) = (@COND nat True m).
Proof. exact (MK_COMB (@lem233538 m n h1) (@lem233539 m)). Qed.
Lemma lem233541 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem233542 (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n) = (@COND nat True m n).
Proof. exact (MK_COMB (@lem233540 m n h1) (@lem233541 n)). Qed.
Lemma lem233544 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem233545 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem233544 nat t2 t1). Qed.
Lemma lem233546 (n : nat) (m : nat) : (@COND nat True m n) = m.
Proof. exact (@lem233545 n m). Qed.
Lemma lem233547 (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n) = m.
Proof. exact (TRANS (@lem233542 m n h1) (@lem233546 n m)). Qed.
Lemma lem233548 (p : nat) : (Nat.pow p) = (Nat.pow p).
Proof. exact (eq_refl (Nat.pow p)). Qed.
Lemma lem233549 (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term270 p m n) = (Nat.pow p m).
Proof. exact (MK_COMB (@lem233548 p) (@lem233547 m n h1)). Qed.
Lemma lem233550 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem233551 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term271 x p m n) = (term46 x p m).
Proof. exact (MK_COMB (@lem233550 x) (@lem233549 p m n h1)). Qed.
Lemma lem233552 (x : nat) (m : nat) (p : nat) (n : nat) : (term52 x m p n) = (term52 x m p n).
Proof. exact (eq_refl (term52 x m p n)). Qed.
Lemma lem233553 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term50 x m p n) = (term271 x p m n)) = ((term50 x m p n) = (term46 x p m)).
Proof. exact (MK_COMB (@lem233552 x m p n) (@lem233551 x p m n h1)). Qed.
Lemma lem233556 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term50 x m p n) = (term46 x p m)) = ((term50 x m p n) = (term271 x p m n)).
Proof. exact (SYM (@lem233553 x p m n h1)). Qed.
Lemma lem233570 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem233575 (m : nat) (n : nat) (h1 : term34 m n) : (Peano.le m n) = False.
Proof. exact (@lem233570 m n (@lem231418 m n h1)). Qed.
Lemma lem233576 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem233577 (m : nat) (n : nat) (h1 : term34 m n) : (term74 m n) = (@COND nat False).
Proof. exact (MK_COMB (@lem233576) (@lem233575 m n h1)). Qed.
Lemma lem233578 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem233579 (m : nat) (n : nat) (h1 : term34 m n) : (term75 n m) = (@COND nat False m).
Proof. exact (MK_COMB (@lem233577 m n h1) (@lem233578 m)). Qed.
Lemma lem233580 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem233581 (m : nat) (n : nat) (h1 : term34 m n) : (term38 m n) = (@COND nat False m n).
Proof. exact (MK_COMB (@lem233579 m n h1) (@lem233580 n)). Qed.
Lemma lem233583 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem233584 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem233583 nat t1 t2). Qed.
Lemma lem233585 (m : nat) (n : nat) : (@COND nat False m n) = n.
Proof. exact (@lem233584 m n). Qed.
Lemma lem233586 (m : nat) (n : nat) (h1 : term34 m n) : (term38 m n) = n.
Proof. exact (TRANS (@lem233581 m n h1) (@lem233585 m n)). Qed.
Lemma lem233587 (p : nat) : (Nat.pow p) = (Nat.pow p).
Proof. exact (eq_refl (Nat.pow p)). Qed.
Lemma lem233588 (p : nat) (m : nat) (n : nat) (h1 : term34 m n) : (term270 p m n) = (Nat.pow p n).
Proof. exact (MK_COMB (@lem233587 p) (@lem233586 m n h1)). Qed.
Lemma lem233589 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem233590 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term34 m n) : (term271 x p m n) = (term46 x p n).
Proof. exact (MK_COMB (@lem233589 x) (@lem233588 p m n h1)). Qed.
Lemma lem233591 (x : nat) (m : nat) (p : nat) (n : nat) : (term52 x m p n) = (term52 x m p n).
Proof. exact (eq_refl (term52 x m p n)). Qed.
Lemma lem233592 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term34 m n) : ((term50 x m p n) = (term271 x p m n)) = ((term50 x m p n) = (term46 x p n)).
Proof. exact (MK_COMB (@lem233591 x m p n) (@lem233590 x p m n h1)). Qed.
Lemma lem233595 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term34 m n) : ((term50 x m p n) = (term46 x p n)) = ((term50 x m p n) = (term271 x p m n)).
Proof. exact (SYM (@lem233592 x p m n h1)). Qed.
Lemma lem233597 (n : nat) (m : nat) : (Peano.le m n) = (term31 n m).
Proof. exact (EQ_MP (@lem231412 n m) (@lem231411 m n)). Qed.
Lemma lem233598 (m : nat) (n : nat) (h1 : Peano.le m n) : term31 n m.
Proof. exact (EQ_MP (@lem233597 n m) (@lem231417 m n h1)). Qed.
Lemma lem233599 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem233600 (x : nat) (p : nat) (m : nat) : (term272 x p m) = (term272 x p m).
Proof. exact (eq_refl (term272 x p m)). Qed.
Lemma lem233601 (x : nat) (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term273 x p m n) = (term274 x p m d).
Proof. exact (MK_COMB (@lem233600 x p m) (@lem233599 n m d h1)). Qed.
Lemma lem233602 (d : nat) (x : nat) (p : nat) (m : nat) : (term274 x p m d) = ((term275 x p m d) = (term46 x p m)).
Proof. exact (eq_refl (term274 x p m d)). Qed.
Lemma lem233603 (x : nat) (p : nat) (m : nat) (n : nat) : (term276 x p m n) = (term276 x p m n).
Proof. exact (eq_refl (term276 x p m n)). Qed.
Lemma lem233604 (n : nat) (d : nat) (x : nat) (p : nat) (m : nat) : ((term273 x p m n) = (term274 x p m d)) = ((term273 x p m n) = ((term275 x p m d) = (term46 x p m))).
Proof. exact (MK_COMB (@lem233603 x p m n) (@lem233602 d x p m)). Qed.
Lemma lem233605 (n : nat) (x : nat) (p : nat) (m : nat) : (term273 x p m n) = ((term50 x m p n) = (term46 x p m)).
Proof. exact (eq_refl (term273 x p m n)). Qed.
Lemma lem233606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem233607 (n : nat) (x : nat) (p : nat) (m : nat) : (term276 x p m n) = (term277 n x p m).
Proof. exact (MK_COMB (@lem233606) (@lem233605 n x p m)). Qed.
Lemma lem233608 (d : nat) (x : nat) (p : nat) (m : nat) : ((term275 x p m d) = (term46 x p m)) = ((term275 x p m d) = (term46 x p m)).
Proof. exact (eq_refl ((term275 x p m d) = (term46 x p m))). Qed.
Lemma lem233609 (n : nat) (d : nat) (x : nat) (p : nat) (m : nat) : ((term273 x p m n) = ((term275 x p m d) = (term46 x p m))) = (((term50 x m p n) = (term46 x p m)) = ((term275 x p m d) = (term46 x p m))).
Proof. exact (MK_COMB (@lem233607 n x p m) (@lem233608 d x p m)). Qed.
Lemma lem233610 (n : nat) (d : nat) (x : nat) (p : nat) (m : nat) : ((term273 x p m n) = (term274 x p m d)) = (((term50 x m p n) = (term46 x p m)) = ((term275 x p m d) = (term46 x p m))).
Proof. exact (TRANS (@lem233604 n d x p m) (@lem233609 n d x p m)). Qed.
Lemma lem233611 (x : nat) (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term50 x m p n) = (term46 x p m)) = ((term275 x p m d) = (term46 x p m)).
Proof. exact (EQ_MP (@lem233610 n d x p m) (@lem233601 x p n m d h1)). Qed.
Lemma lem233612 (x : nat) (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((term275 x p m d) = (term46 x p m)) = ((term50 x m p n) = (term46 x p m)).
Proof. exact (SYM (@lem233611 x p n m d h1)). Qed.
Lemma lem233614 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem231406 n m) (@lem231405 n m)). Qed.
Lemma lem233615 (d : nat) (x : nat) (p : nat) (m : nat) : term278 d x p m.
Proof. exact (@lem233614 (term279 p m d) (term46 x p m)). Qed.
Lemma lem233617 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem231383 m p) (@lem231382 m p)). Qed.
Lemma lem233618 (x : nat) (p : nat) (m : nat) (d : nat) : term280 x p m d.
Proof. exact (@lem233617 (term46 x p m) (term279 p m d)). Qed.
Lemma lem233619 (m : nat) : term281 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem233620 (m : nat) : (term281 m) = (term282 m).
Proof. exact (eq_refl (term281 m)). Qed.
Lemma lem233621 (m : nat) : term282 m.
Proof. exact (EQ_MP (@lem233620 m) (@lem233619 m)). Qed.
Lemma lem233622 (m : nat) (n : nat) : term283 m n.
Proof. exact (@lem233621 m n). Qed.
Lemma lem233623 (m : nat) (n : nat) : (term283 m n) = (term284 m n).
Proof. exact (eq_refl (term283 m n)). Qed.
Lemma lem233624 (m : nat) (n : nat) : term284 m n.
Proof. exact (EQ_MP (@lem233623 m n) (@lem233622 m n)). Qed.
Lemma lem233625 (m : nat) (n : nat) : (term284 m n) = ((term284 m n) = True).
Proof. exact (@lem7 (term284 m n)). Qed.
Lemma lem233627 (x : nat) : term285 x.
Proof. exact (@lem149199 x). Qed.
Lemma lem233628 (x : nat) : (term285 x) = (term286 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem233629 (x : nat) : term286 x.
Proof. exact (EQ_MP (@lem233628 x) (@lem233627 x)). Qed.
Lemma lem233630 (x : nat) (m : nat) : term287 x m.
Proof. exact (@lem233629 x m). Qed.
Lemma lem233631 (x : nat) (m : nat) : (term287 x m) = (term288 x m).
Proof. exact (eq_refl (term287 x m)). Qed.
Lemma lem233632 (x : nat) (m : nat) : term288 x m.
Proof. exact (EQ_MP (@lem233631 x m) (@lem233630 x m)). Qed.
Lemma lem233633 (x : nat) (m : nat) (n : nat) : term289 x m n.
Proof. exact (@lem233632 x m n). Qed.
Lemma lem233634 (x : nat) (m : nat) (n : nat) : (term289 x m n) = ((term290 m x n) = (term291 x m n)).
Proof. exact (eq_refl (term289 x m n)). Qed.
Lemma lem233636 (m : nat) : term292 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem233637 (m : nat) : (term292 m) = (term293 m).
Proof. exact (eq_refl (term292 m)). Qed.
Lemma lem233638 (m : nat) : term293 m.
Proof. exact (EQ_MP (@lem233637 m) (@lem233636 m)). Qed.
Lemma lem233639 (m : nat) (n : nat) : term294 m n.
Proof. exact (@lem233638 m n). Qed.
Lemma lem233640 (m : nat) (n : nat) : (term294 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term295 m n)).
Proof. exact (eq_refl (term294 m n)). Qed.
Lemma lem233642 (m : nat) : term296 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem233643 (m : nat) : (term296 m) = (term297 m).
Proof. exact (eq_refl (term296 m)). Qed.
Lemma lem233644 (m : nat) : term297 m.
Proof. exact (EQ_MP (@lem233643 m) (@lem233642 m)). Qed.
Lemma lem233645 (m : nat) (n : nat) : term298 m n.
Proof. exact (@lem233644 m n). Qed.
Lemma lem233646 (m : nat) (n : nat) : (term298 m n) = (term299 m n).
Proof. exact (eq_refl (term298 m n)). Qed.
Lemma lem233647 (m : nat) (n : nat) : term299 m n.
Proof. exact (EQ_MP (@lem233646 m n) (@lem233645 m n)). Qed.
Lemma lem233648 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem233649 (m : nat) (n : nat) (h1 : term41 n) : term300 m n.
Proof. exact (@lem233647 m n (@lem233648 n h1)). Qed.
Lemma lem233650 (m : nat) (n : nat) (h1 : term41 n) : term301 m n.
Proof. exact (proj2 (@lem233649 m n h1)). Qed.
Lemma lem233651 (m : nat) (n : nat) : (term301 m n) = ((term301 m n) = True).
Proof. exact (@lem7 (term301 m n)). Qed.
Lemma lem233652 (m : nat) (n : nat) (h1 : term41 n) : (term301 m n) = True.
Proof. exact (EQ_MP (@lem233651 m n) (@lem233650 m n h1)). Qed.
Lemma lem233669 (p : nat) : term83 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem233691 (m : nat) (n : nat) : term302 m n.
Proof. exact (fun h0 : term41 n => @lem233652 m n h0). Qed.
Lemma lem233692 (x : nat) (p : nat) (m : nat) : term303 x p m.
Proof. exact (@lem233691 x (Nat.pow p m)). Qed.
Lemma lem233698 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term295 m n).
Proof. exact (EQ_MP (@lem233640 m n) (@lem233639 m n)). Qed.
Lemma lem233699 (p : nat) (m : nat) : ((Nat.pow p m) = (NUMERAL 0)) = (term295 p m).
Proof. exact (@lem233698 p m). Qed.
Lemma lem233709 (p : nat) (h1 : term41 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem233669 p (@lem231449 p h1)). Qed.
Lemma lem233712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem233713 (p : nat) (h1 : term41 p) : (term304 p) = (and False).
Proof. exact (MK_COMB (@lem233712) (@lem233709 p h1)). Qed.
Lemma lem233740 (m : nat) : (term41 m) = (term41 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem233741 (m : nat) (p : nat) (h1 : term41 p) : (term295 p m) = (term305 m).
Proof. exact (MK_COMB (@lem233713 p h1) (@lem233740 m)). Qed.
Lemma lem233743 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem233744 (m : nat) : (term305 m) = False.
Proof. exact (@lem233743 (term41 m)). Qed.
Lemma lem233747 (m : nat) (p : nat) (h1 : term41 p) : (term295 p m) = False.
Proof. exact (TRANS (@lem233741 m p h1) (@lem233744 m)). Qed.
Lemma lem233748 (m : nat) (p : nat) (h1 : term41 p) : ((Nat.pow p m) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem233699 p m) (@lem233747 m p h1)). Qed.
Lemma lem233749 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem233750 (m : nat) (p : nat) (h1 : term41 p) : (term306 p m) = (~ False).
Proof. exact (MK_COMB (@lem233749) (@lem233748 m p h1)). Qed.
Lemma lem233752 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem233755 (m : nat) (p : nat) (h1 : term41 p) : (term306 p m) = True.
Proof. exact (TRANS (@lem233750 m p h1) (@lem233752)). Qed.
Lemma lem233756 (m : nat) (p : nat) (h1 : term41 p) : True = (term306 p m).
Proof. exact (SYM (@lem233755 m p h1)). Qed.
Lemma lem233757 (m : nat) (p : nat) (h1 : term41 p) : term306 p m.
Proof. exact (EQ_MP (@lem233756 m p h1) (@lem0)). Qed.
Lemma lem233758 (x : nat) (m : nat) (p : nat) (h1 : term41 p) : (term307 x p m) = True.
Proof. exact (@lem233692 x p m (@lem233757 m p h1)). Qed.
Lemma lem233761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem233762 (x : nat) (m : nat) (p : nat) (h1 : term41 p) : (term308 x p m) = (and True).
Proof. exact (MK_COMB (@lem233761) (@lem233758 x m p h1)). Qed.
Lemma lem233770 (x : nat) (m : nat) (n : nat) : (term290 m x n) = (term291 x m n).
Proof. exact (EQ_MP (@lem233634 x m n) (@lem233633 x m n)). Qed.
Lemma lem233771 (p : nat) (m : nat) (d : nat) : (term309 p m d) = (term310 p m d).
Proof. exact (@lem233770 p m (Nat.add m d)). Qed.
Lemma lem233777 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term311 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem233778 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term312 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem233777 _2963 g t e g' t' e'). Qed.
Lemma lem233779 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term313 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem233778 _2963 g t e g' t'). Qed.
Lemma lem233780 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term314 _2963 g t e.
Proof. exact (fun g' : Prop => @lem233779 _2963 g t e g'). Qed.
Lemma lem233781 (g : Prop) (t : Prop) (e : Prop) : term315 g t e.
Proof. exact (@lem233780 Prop g t e). Qed.
Lemma lem233782 (p : nat) (m : nat) (d : nat) : term316 p m d.
Proof. exact (@lem233781 (p = (NUMERAL 0)) (term317 m d) (term318 p m d)). Qed.
Lemma lem233783 (p : nat) (m : nat) (d : nat) (g' : Prop) : term319 p m d g'.
Proof. exact (@lem233782 p m d g'). Qed.
Lemma lem233784 (p : nat) (m : nat) (d : nat) (g' : Prop) : (term319 p m d g') = (term320 p m d g').
Proof. exact (eq_refl (term319 p m d g')). Qed.
Lemma lem233785 (p : nat) (m : nat) (d : nat) (g' : Prop) : term320 p m d g'.
Proof. exact (EQ_MP (@lem233784 p m d g') (@lem233783 p m d g')). Qed.
Lemma lem233786 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) : term321 p m d g' t'.
Proof. exact (@lem233785 p m d g' t'). Qed.
Lemma lem233787 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) : (term321 p m d g' t') = (term322 p m d g' t').
Proof. exact (eq_refl (term321 p m d g' t')). Qed.
Lemma lem233788 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) : term322 p m d g' t'.
Proof. exact (EQ_MP (@lem233787 p m d g' t') (@lem233786 p m d g' t')). Qed.
Lemma lem233789 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term323 p m d g' t' e'.
Proof. exact (@lem233788 p m d g' t' e'). Qed.
Lemma lem233790 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) (e' : Prop) : (term323 p m d g' t' e') = (term324 p m d g' t' e').
Proof. exact (eq_refl (term323 p m d g' t' e')). Qed.
Lemma lem233791 (p : nat) (m : nat) (d : nat) (g' : Prop) (t' : Prop) (e' : Prop) : term324 p m d g' t' e'.
Proof. exact (EQ_MP (@lem233790 p m d g' t' e') (@lem233789 p m d g' t' e')). Qed.
Lemma lem233793 (p : nat) (h1 : term41 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem233669 p (@lem231449 p h1)). Qed.
Lemma lem233796 (p : nat) (m : nat) (d : nat) (t' : Prop) (e' : Prop) : term325 p m d t' e'.
Proof. exact (@lem233791 p m d False t' e'). Qed.
Lemma lem233797 (m : nat) (d : nat) (t' : Prop) (e' : Prop) (p : nat) (h1 : term41 p) : term326 p m d t' e'.
Proof. exact (@lem233796 p m d t' e' (@lem233793 p h1)). Qed.
Lemma lem233808 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem233809 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem233808 p q p' q'). Qed.
Lemma lem233810 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem233809 p q p'). Qed.
Lemma lem233811 (m : nat) (d : nat) : term330 m d.
Proof. exact (@lem233810 (m = (NUMERAL 0)) ((Nat.add m d) = (NUMERAL 0))). Qed.
Lemma lem233812 (m : nat) (d : nat) (p' : Prop) : term331 m d p'.
Proof. exact (@lem233811 m d p'). Qed.
Lemma lem233813 (m : nat) (d : nat) (p' : Prop) : (term331 m d p') = (term332 m d p').
Proof. exact (eq_refl (term331 m d p')). Qed.
Lemma lem233814 (m : nat) (d : nat) (p' : Prop) : term332 m d p'.
Proof. exact (EQ_MP (@lem233813 m d p') (@lem233812 m d p')). Qed.
Lemma lem233815 (m : nat) (d : nat) (p' : Prop) (q' : Prop) : term333 m d p' q'.
Proof. exact (@lem233814 m d p' q'). Qed.
Lemma lem233816 (m : nat) (d : nat) (p' : Prop) (q' : Prop) : (term333 m d p' q') = (term334 m d p' q').
Proof. exact (eq_refl (term333 m d p' q')). Qed.
Lemma lem233817 (m : nat) (d : nat) (p' : Prop) (q' : Prop) : term334 m d p' q'.
Proof. exact (EQ_MP (@lem233816 m d p' q') (@lem233815 m d p' q')). Qed.
Lemma lem233834 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem233835 (d : nat) (m : nat) (q' : Prop) : term335 d m q'.
Proof. exact (@lem233817 m d (m = (NUMERAL 0)) q'). Qed.
Lemma lem233836 (d : nat) (m : nat) (q' : Prop) : term336 d m q'.
Proof. exact (@lem233835 d m q' (@lem233834 m)). Qed.
Lemma lem233853 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem233860 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem233861 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.add m) = term337.
Proof. exact (MK_COMB (@lem233860) (@lem233853 m h1)). Qed.
Lemma lem233874 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem233875 (d : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.add m d) = (term338 d).
Proof. exact (MK_COMB (@lem233861 m h1) (@lem233874 d)). Qed.
Lemma lem233890 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem233891 (d : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term339 m d) = (term340 d).
Proof. exact (MK_COMB (@lem233890) (@lem233875 d m h1)). Qed.
Lemma lem233916 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem233917 (d : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((Nat.add m d) = (NUMERAL 0)) = ((term338 d) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem233891 d m h1) (@lem233916)). Qed.
Lemma lem233946 (m : nat) (d : nat) : term341 m d.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem233917 d m h0). Qed.
Lemma lem233947 (m : nat) (d : nat) : term342 m d.
Proof. exact (@lem233836 d m ((term338 d) = (NUMERAL 0))). Qed.
Lemma lem233948 (m : nat) (d : nat) : (term317 m d) = (term343 m d).
Proof. exact (@lem233947 m d (@lem233946 m d)). Qed.
Lemma lem234066 (m : nat) (d : nat) : term344 m d.
Proof. exact (fun h0 : False => @lem233948 m d). Qed.
Lemma lem234067 (m : nat) (d : nat) (e' : Prop) (p : nat) (h1 : term41 p) : term345 p m d e'.
Proof. exact (@lem233797 m d (term343 m d) e' p h1). Qed.
Lemma lem234068 (m : nat) (d : nat) (e' : Prop) (p : nat) (h1 : term41 p) : term346 p m d e'.
Proof. exact (@lem234067 m d e' p h1 (@lem234066 m d)). Qed.
Lemma lem234103 (m : nat) (n : nat) : (term284 m n) = True.
Proof. exact (EQ_MP (@lem233625 m n) (@lem233624 m n)). Qed.
Lemma lem234104 (m : nat) (d : nat) : (term284 m d) = True.
Proof. exact (@lem234103 m d). Qed.
Lemma lem234107 (p : nat) : (term347 p) = (term347 p).
Proof. exact (eq_refl (term347 p)). Qed.
Lemma lem234108 (m : nat) (d : nat) (p : nat) : (term318 p m d) = (term348 p).
Proof. exact (MK_COMB (@lem234107 p) (@lem234104 m d)). Qed.
Lemma lem234110 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem234111 (p : nat) : (term348 p) = True.
Proof. exact (@lem234110 (p = term67)). Qed.
Lemma lem234114 (p : nat) (m : nat) (d : nat) : (term318 p m d) = True.
Proof. exact (TRANS (@lem234108 m d p) (@lem234111 p)). Qed.
Lemma lem234115 (p : nat) (m : nat) (d : nat) : term349 p m d.
Proof. exact (fun h0 : ~ False => @lem234114 p m d). Qed.
Lemma lem234116 (m : nat) (d : nat) (p : nat) (h1 : term41 p) : term350 p m d.
Proof. exact (@lem234068 m d True p h1). Qed.
Lemma lem234117 (m : nat) (d : nat) (p : nat) (h1 : term41 p) : (term310 p m d) = (term351 m d).
Proof. exact (@lem234116 m d p h1 (@lem234115 p m d)). Qed.
Lemma lem234119 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem234120 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem234119 Prop t1 t2). Qed.
Lemma lem234121 (m : nat) (d : nat) : (term351 m d) = True.
Proof. exact (@lem234120 (term343 m d) True). Qed.
Lemma lem234124 (m : nat) (d : nat) (p : nat) (h1 : term41 p) : (term310 p m d) = True.
Proof. exact (TRANS (@lem234117 m d p h1) (@lem234121 m d)). Qed.
Lemma lem234125 (m : nat) (d : nat) (p : nat) (h1 : term41 p) : (term309 p m d) = True.
Proof. exact (TRANS (@lem233771 p m d) (@lem234124 m d p h1)). Qed.
Lemma lem234126 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : (term352 x p m d) = (True /\ True).
Proof. exact (MK_COMB (@lem233762 x m p h1) (@lem234125 m d p h1)). Qed.
Lemma lem234128 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem234129 : (True /\ True) = True.
Proof. exact (@lem234128 True). Qed.
Lemma lem234132 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : (term352 x p m d) = True.
Proof. exact (TRANS (@lem234126 x m d p h1) (@lem234129)). Qed.
Lemma lem234133 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : True = (term352 x p m d).
Proof. exact (SYM (@lem234132 x m d p h1)). Qed.
Lemma lem234134 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : term352 x p m d.
Proof. exact (EQ_MP (@lem234133 x m d p h1) (@lem0)). Qed.
Lemma lem234135 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : term353 x p m d.
Proof. exact (ex_intro (term354 x p m d) (Nat.pow p m) (@lem234134 x m d p h1)). Qed.
Lemma lem234136 (x : nat) (m : nat) (d : nat) (p : nat) (h1 : term41 p) : term355 x p m d.
Proof. exact (@lem233618 x p m d (@lem234135 x m d p h1)). Qed.
Lemma lem234137 (d : nat) (x : nat) (m : nat) (p : nat) (h1 : term41 p) : (term275 x p m d) = (term46 x p m).
Proof. exact (@lem233615 d x p m (@lem234136 x m d p h1)). Qed.
Lemma lem234138 (x : nat) (p : nat) (n : nat) (m : nat) (d : nat) (h1 : term41 p) (h2 : n = (Nat.add m d)) : (term50 x m p n) = (term46 x p m).
Proof. exact (EQ_MP (@lem233612 x p n m d h2) (@lem234137 d x m p h1)). Qed.
Lemma lem234139 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term41 p) (h2 : Peano.le m n) : (term50 x m p n) = (term46 x p m).
Proof. exact (ex_elim (@lem233598 m n h2) (fun d : nat => fun h0 : term356 n m d => @lem234138 x p n m d h1 h0)). Qed.
Lemma lem234140 (m : nat) (n : nat) (h1 : term31 m n) : term31 m n.
Proof. exact (h1). Qed.
Lemma lem234141 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem234142 (x : nat) (p : nat) (n : nat) : (term357 x p n) = (term357 x p n).
Proof. exact (eq_refl (term357 x p n)). Qed.
Lemma lem234143 (x : nat) (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term358 x p n m) = (term359 x p n d).
Proof. exact (MK_COMB (@lem234142 x p n) (@lem234141 m n d h1)). Qed.
Lemma lem234144 (d : nat) (x : nat) (p : nat) (n : nat) : (term359 x p n d) = ((term360 x d p n) = (term46 x p n)).
Proof. exact (eq_refl (term359 x p n d)). Qed.
Lemma lem234145 (x : nat) (p : nat) (n : nat) (m : nat) : (term361 x p n m) = (term361 x p n m).
Proof. exact (eq_refl (term361 x p n m)). Qed.
Lemma lem234146 (m : nat) (d : nat) (x : nat) (p : nat) (n : nat) : ((term358 x p n m) = (term359 x p n d)) = ((term358 x p n m) = ((term360 x d p n) = (term46 x p n))).
Proof. exact (MK_COMB (@lem234145 x p n m) (@lem234144 d x p n)). Qed.
Lemma lem234147 (m : nat) (x : nat) (p : nat) (n : nat) : (term358 x p n m) = ((term50 x m p n) = (term46 x p n)).
Proof. exact (eq_refl (term358 x p n m)). Qed.
Lemma lem234148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234149 (m : nat) (x : nat) (p : nat) (n : nat) : (term361 x p n m) = (term362 m x p n).
Proof. exact (MK_COMB (@lem234148) (@lem234147 m x p n)). Qed.
Lemma lem234150 (d : nat) (x : nat) (p : nat) (n : nat) : ((term360 x d p n) = (term46 x p n)) = ((term360 x d p n) = (term46 x p n)).
Proof. exact (eq_refl ((term360 x d p n) = (term46 x p n))). Qed.
Lemma lem234151 (m : nat) (d : nat) (x : nat) (p : nat) (n : nat) : ((term358 x p n m) = ((term360 x d p n) = (term46 x p n))) = (((term50 x m p n) = (term46 x p n)) = ((term360 x d p n) = (term46 x p n))).
Proof. exact (MK_COMB (@lem234149 m x p n) (@lem234150 d x p n)). Qed.
Lemma lem234152 (m : nat) (d : nat) (x : nat) (p : nat) (n : nat) : ((term358 x p n m) = (term359 x p n d)) = (((term50 x m p n) = (term46 x p n)) = ((term360 x d p n) = (term46 x p n))).
Proof. exact (TRANS (@lem234146 m d x p n) (@lem234151 m d x p n)). Qed.
Lemma lem234153 (x : nat) (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((term50 x m p n) = (term46 x p n)) = ((term360 x d p n) = (term46 x p n)).
Proof. exact (EQ_MP (@lem234152 m d x p n) (@lem234143 x p m n d h1)). Qed.
Lemma lem234154 (x : nat) (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((term360 x d p n) = (term46 x p n)) = ((term50 x m p n) = (term46 x p n)).
Proof. exact (SYM (@lem234153 x p m n d h1)). Qed.
Lemma lem234156 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem234157 (m : nat) (n : nat) : (term31 m n) = (term363 m n).
Proof. exact (@lem234156 (term31 m n)). Qed.
Lemma lem234158 (m : nat) (n : nat) : (term363 m n) = (term31 m n).
Proof. exact (SYM (@lem234157 m n)). Qed.
Lemma lem234159 (m : nat) (n : nat) (h1 : term364 m n) : term364 m n.
Proof. exact (h1). Qed.
Lemma lem234162 (p : nat) (m : nat) (n : nat) (h1 : term365 p m n) : term365 p m n.
Proof. exact (h1). Qed.
Lemma lem234163 (p : nat) (m : nat) (n : nat) : term366 p m n.
Proof. exact (fun h0 : term365 p m n => @lem234162 p m n h0). Qed.
Lemma lem234164 (p : nat) (m : nat) (n : nat) (h1 : term366 p m n) : term366 p m n.
Proof. exact (h1). Qed.
Lemma lem234165 (p : nat) (m : nat) (n : nat) (h1 : term365 p m n) : term365 p m n.
Proof. exact (h1). Qed.
Lemma lem234166 (p : nat) (m : nat) (n : nat) (h1 : term365 p m n) (h2 : term366 p m n) : term365 p m n.
Proof. exact (@lem234164 p m n h2 (@lem234165 p m n h1)). Qed.
Lemma lem234167 (p : nat) (m : nat) (n : nat) (h1 : term365 p m n) : term367 p m n.
Proof. exact (fun h0 : term366 p m n => @lem234166 p m n h1 h0). Qed.
Lemma lem234168 (p : nat) (m : nat) (n : nat) (h1 : term366 p m n) : term366 p m n.
Proof. exact (h1). Qed.
Lemma lem234169 (p : nat) (m : nat) (n : nat) (h1 : term365 p m n) (h2 : term366 p m n) : term365 p m n.
Proof. exact (@lem234167 p m n h1 (@lem234168 p m n h2)). Qed.
Lemma lem234170 (p : nat) (m : nat) (n : nat) (h1 : term366 p m n) : term366 p m n.
Proof. exact (fun h0 : term365 p m n => @lem234169 p m n h0 h1). Qed.
Lemma lem234171 (p : nat) (m : nat) (n : nat) : term368 p m n.
Proof. exact (fun h0 : term366 p m n => @lem234170 p m n h0). Qed.
Lemma lem234174 (p : nat) (m : nat) (n : nat) : term366 p m n.
Proof. exact (@lem234171 p m n (@lem234163 p m n)). Qed.
Lemma lem234212 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem234213 : term369 = term370.
Proof. exact (@lem234212 term371). Qed.
Lemma lem234268 : term372 = term372.
Proof. exact (eq_refl term372). Qed.
Lemma lem234269 : term373 = term374.
Proof. exact (MK_COMB (@lem234268) (@lem234213)). Qed.
Lemma lem234272 (m : nat) (n : nat) : (term375 m n) = (term375 m n).
Proof. exact (eq_refl (term375 m n)). Qed.
Lemma lem234273 (m : nat) (n : nat) : (term376 m n) = (term377 m n).
Proof. exact (MK_COMB (@lem234272 m n) (@lem234269)). Qed.
Lemma lem234276 (m : nat) (n : nat) : (term378 m n) = (term378 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem234277 (m : nat) (n : nat) : (term379 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem234276 m n) (@lem234273 m n)). Qed.
Lemma lem234280 (p : nat) : (term96 p) = (term96 p).
Proof. exact (eq_refl (term96 p)). Qed.
Lemma lem234281 (p : nat) (m : nat) (n : nat) : (term365 p m n) = (term381 p m n).
Proof. exact (MK_COMB (@lem234280 p) (@lem234277 m n)). Qed.
Lemma lem234284 (m : nat) (n : nat) : (term382 m n) = (term383 m n).
Proof. exact (fun_ext (fun p : nat => @lem234281 p m n)). Qed.
Lemma lem234285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234286 (m : nat) (n : nat) : (term384 m n) = (term385 m n).
Proof. exact (MK_COMB (@lem234285) (@lem234284 m n)). Qed.
Lemma lem234291 (n : nat) : (term386 n) = (term387 n).
Proof. exact (fun_ext (fun m : nat => @lem234286 m n)). Qed.
Lemma lem234292 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234293 (n : nat) : (term388 n) = (term389 n).
Proof. exact (MK_COMB (@lem234292) (@lem234291 n)). Qed.
Lemma lem234298 : term390 = term391.
Proof. exact (fun_ext (fun n : nat => @lem234293 n)). Qed.
Lemma lem234299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234308 : term392 = term393.
Proof. exact (MK_COMB (@lem234299) (@lem234298)). Qed.
Lemma lem234313 (n : nat) (m : nat) : (term394 n m) = (term394 n m).
Proof. exact (eq_refl (term394 n m)). Qed.
Lemma lem234314 (m : nat) : (term395 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem234313 n m)). Qed.
Lemma lem234315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234316 (m : nat) : (term396 m) = (term396 m).
Proof. exact (MK_COMB (@lem234315) (@lem234314 m)). Qed.
Lemma lem234317 : term397 = term397.
Proof. exact (fun_ext (fun m : nat => @lem234316 m)). Qed.
Lemma lem234318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234319 : term371 = term371.
Proof. exact (MK_COMB (@lem234318) (@lem234317)). Qed.
Lemma lem234320 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem234321 : term370 = term370.
Proof. exact (MK_COMB (@lem234320) (@lem234319)). Qed.
Lemma lem234322 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem234323 (n : nat) (m : nat) : (term356 n m) = (term356 n m).
Proof. exact (fun_ext (fun d : nat => @lem234322 n m d)). Qed.
Lemma lem234324 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234325 (n : nat) (m : nat) : (term31 n m) = (term31 n m).
Proof. exact (MK_COMB (@lem234324) (@lem234323 n m)). Qed.
Lemma lem234328 (m : nat) (n : nat) : (term249 m n) = (term249 m n).
Proof. exact (eq_refl (term249 m n)). Qed.
Lemma lem234329 (n : nat) (m : nat) : ((Peano.le m n) = (term31 n m)) = ((Peano.le m n) = (term31 n m)).
Proof. exact (MK_COMB (@lem234328 m n) (@lem234325 n m)). Qed.
Lemma lem234330 (m : nat) : (term398 m) = (term398 m).
Proof. exact (fun_ext (fun n : nat => @lem234329 n m)). Qed.
Lemma lem234331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234332 (m : nat) : (term29 m) = (term29 m).
Proof. exact (MK_COMB (@lem234331) (@lem234330 m)). Qed.
Lemma lem234333 : term399 = term399.
Proof. exact (fun_ext (fun m : nat => @lem234332 m)). Qed.
Lemma lem234334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234335 : term400 = term400.
Proof. exact (MK_COMB (@lem234334) (@lem234333)). Qed.
Lemma lem234336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem234337 : term372 = term372.
Proof. exact (MK_COMB (@lem234336) (@lem234335)). Qed.
Lemma lem234338 : term374 = term374.
Proof. exact (MK_COMB (@lem234337) (@lem234321)). Qed.
Lemma lem234339 (m : nat) (n : nat) (d : nat) : (m = (Nat.add n d)) = (m = (Nat.add n d)).
Proof. exact (eq_refl (m = (Nat.add n d))). Qed.
Lemma lem234340 (m : nat) (n : nat) : (term356 m n) = (term356 m n).
Proof. exact (fun_ext (fun d : nat => @lem234339 m n d)). Qed.
Lemma lem234341 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234342 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem234341) (@lem234340 m n)). Qed.
Lemma lem234343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem234344 (m : nat) (n : nat) : (term364 m n) = (term364 m n).
Proof. exact (MK_COMB (@lem234343) (@lem234342 m n)). Qed.
Lemma lem234345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem234346 (m : nat) (n : nat) : (term375 m n) = (term375 m n).
Proof. exact (MK_COMB (@lem234345) (@lem234344 m n)). Qed.
Lemma lem234347 (m : nat) (n : nat) : (term377 m n) = (term377 m n).
Proof. exact (MK_COMB (@lem234346 m n) (@lem234338)). Qed.
Lemma lem234352 (m : nat) (n : nat) : (term378 m n) = (term378 m n).
Proof. exact (eq_refl (term378 m n)). Qed.
Lemma lem234353 (m : nat) (n : nat) : (term380 m n) = (term380 m n).
Proof. exact (MK_COMB (@lem234352 m n) (@lem234347 m n)). Qed.
Lemma lem234358 (p : nat) : (term96 p) = (term96 p).
Proof. exact (eq_refl (term96 p)). Qed.
Lemma lem234359 (p : nat) (m : nat) (n : nat) : (term381 p m n) = (term381 p m n).
Proof. exact (MK_COMB (@lem234358 p) (@lem234353 m n)). Qed.
Lemma lem234360 (m : nat) (n : nat) : (term383 m n) = (term383 m n).
Proof. exact (fun_ext (fun p : nat => @lem234359 p m n)). Qed.
Lemma lem234361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234362 (m : nat) (n : nat) : (term385 m n) = (term385 m n).
Proof. exact (MK_COMB (@lem234361) (@lem234360 m n)). Qed.
Lemma lem234363 (n : nat) : (term387 n) = (term387 n).
Proof. exact (fun_ext (fun m : nat => @lem234362 m n)). Qed.
Lemma lem234364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234365 (n : nat) : (term389 n) = (term389 n).
Proof. exact (MK_COMB (@lem234364) (@lem234363 n)). Qed.
Lemma lem234366 : term391 = term391.
Proof. exact (fun_ext (fun n : nat => @lem234365 n)). Qed.
Lemma lem234367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234368 : term393 = term393.
Proof. exact (MK_COMB (@lem234367) (@lem234366)). Qed.
Lemma lem234435 : term392 = term393.
Proof. exact (TRANS (@lem234308) (@lem234368)). Qed.
Lemma lem234436 : term393 = term392.
Proof. exact (SYM (@lem234435)). Qed.
Lemma lem234439 (m : nat) (n : nat) (h1 : term364 m n) : term364 m n.
Proof. exact (h1). Qed.
Lemma lem234440 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem234441 (h1 : term371) : term371.
Proof. exact (h1). Qed.
Lemma lem234453 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem234455 (P : nat -> Prop) : (term401 P) = (term402 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem234456 (m : nat) (n : nat) : (term364 m n) = (term403 m n).
Proof. exact (@lem234455 (term356 m n)). Qed.
Lemma lem234457 (m : nat) (n : nat) (d : nat) : (term404 m n d) = (m = (Nat.add n d)).
Proof. exact (eq_refl (term404 m n d)). Qed.
Lemma lem234458 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem234460 (m : nat) (n : nat) (d : nat) : (term405 m n d) = (term406 m n d).
Proof. exact (MK_COMB (@lem234458) (@lem234457 m n d)). Qed.
Lemma lem234461 (m : nat) (n : nat) : (term407 m n) = (term408 m n).
Proof. exact (fun_ext (fun d : nat => @lem234460 m n d)). Qed.
Lemma lem234462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234463 (m : nat) (n : nat) : (term403 m n) = (term409 m n).
Proof. exact (MK_COMB (@lem234462) (@lem234461 m n)). Qed.
Lemma lem234472 (m : nat) (n : nat) : (term364 m n) = (term409 m n).
Proof. exact (TRANS (@lem234456 m n) (@lem234463 m n)). Qed.
Lemma lem234473 (m : nat) (n : nat) (h1 : term364 m n) : term409 m n.
Proof. exact (EQ_MP (@lem234472 m n) (@lem234439 m n h1)). Qed.
Lemma lem234477 (n : nat) (m : nat) (d : nat) : (n = (Nat.add m d)) = (n = (Nat.add m d)).
Proof. exact (eq_refl (n = (Nat.add m d))). Qed.
Lemma lem234478 (P : nat -> Prop) : (term401 P) = (term402 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem234479 (n : nat) (m : nat) : (term364 n m) = (term403 n m).
Proof. exact (@lem234478 (term356 n m)). Qed.
Lemma lem234480 (n : nat) (m : nat) (d : nat) : (term404 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term404 n m d)). Qed.
Lemma lem234481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem234483 (n : nat) (m : nat) (d : nat) : (term405 n m d) = (term406 n m d).
Proof. exact (MK_COMB (@lem234481) (@lem234480 n m d)). Qed.
Lemma lem234484 (n : nat) (m : nat) : (term407 n m) = (term408 n m).
Proof. exact (fun_ext (fun d : nat => @lem234483 n m d)). Qed.
Lemma lem234485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234486 (n : nat) (m : nat) : (term403 n m) = (term409 n m).
Proof. exact (MK_COMB (@lem234485) (@lem234484 n m)). Qed.
Lemma lem234487 (n : nat) (m : nat) : (term364 n m) = (term409 n m).
Proof. exact (TRANS (@lem234479 n m) (@lem234486 n m)). Qed.
Lemma lem234488 (n : nat) (m : nat) : (term356 n m) = (term356 n m).
Proof. exact (fun_ext (fun d : nat => @lem234477 n m d)). Qed.
Lemma lem234489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234490 (n : nat) (m : nat) : (term31 n m) = (term31 n m).
Proof. exact (MK_COMB (@lem234489) (@lem234488 n m)). Qed.
Lemma lem234492 (m : nat) (n : nat) : (term410 m n) = (term410 m n).
Proof. exact (eq_refl (term410 m n)). Qed.
Lemma lem234493 (n : nat) (m : nat) : (term411 n m) = (term411 n m).
Proof. exact (MK_COMB (@lem234492 m n) (@lem234490 n m)). Qed.
Lemma lem234495 (m : nat) (n : nat) : (term412 m n) = (term412 m n).
Proof. exact (eq_refl (term412 m n)). Qed.
Lemma lem234496 (n : nat) (m : nat) : (term413 n m) = (term414 n m).
Proof. exact (MK_COMB (@lem234495 m n) (@lem234487 n m)). Qed.
Lemma lem234497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem234498 (n : nat) (m : nat) : (term415 n m) = (term416 n m).
Proof. exact (MK_COMB (@lem234497) (@lem234496 n m)). Qed.
Lemma lem234499 (n : nat) (m : nat) : (term417 n m) = (term418 n m).
Proof. exact (MK_COMB (@lem234498 n m) (@lem234493 n m)). Qed.
Lemma lem234500 (n : nat) (m : nat) : ((Peano.le m n) = (term31 n m)) = (term417 n m).
Proof. exact (@lem17784 (Peano.le m n) (term31 n m)). Qed.
Lemma lem234501 (n : nat) (m : nat) : ((Peano.le m n) = (term31 n m)) = (term418 n m).
Proof. exact (TRANS (@lem234500 n m) (@lem234499 n m)). Qed.
Lemma lem234502 (m : nat) : (term398 m) = (term419 m).
Proof. exact (fun_ext (fun n : nat => @lem234501 n m)). Qed.
Lemma lem234503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234504 (m : nat) : (term29 m) = (term420 m).
Proof. exact (MK_COMB (@lem234503) (@lem234502 m)). Qed.
Lemma lem234505 : term399 = term421.
Proof. exact (fun_ext (fun m : nat => @lem234504 m)). Qed.
Lemma lem234506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234507 : term400 = term422.
Proof. exact (MK_COMB (@lem234506) (@lem234505)). Qed.
Lemma lem234513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem234514 (P : nat -> Prop) (Q : nat -> Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem234513 nat P Q). Qed.
Lemma lem234515 (m : nat) : (term423 m) = (term424 m).
Proof. exact (@lem234514 (term425 m) (term426 m)). Qed.
Lemma lem234516 (n : nat) (m : nat) : (term427 m n) = (term414 n m).
Proof. exact (eq_refl (term427 m n)). Qed.
Lemma lem234517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem234518 (n : nat) (m : nat) : (term428 m n) = (term416 n m).
Proof. exact (MK_COMB (@lem234517) (@lem234516 n m)). Qed.
Lemma lem234519 (n : nat) (m : nat) : (term429 m n) = (term411 n m).
Proof. exact (eq_refl (term429 m n)). Qed.
Lemma lem234520 (n : nat) (m : nat) : (term430 m n) = (term418 n m).
Proof. exact (MK_COMB (@lem234518 n m) (@lem234519 n m)). Qed.
Lemma lem234521 (m : nat) : (term431 m) = (term419 m).
Proof. exact (fun_ext (fun n : nat => @lem234520 n m)). Qed.
Lemma lem234522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234523 (m : nat) : (term423 m) = (term420 m).
Proof. exact (MK_COMB (@lem234522) (@lem234521 m)). Qed.
Lemma lem234524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234525 (m : nat) : (term432 m) = (term433 m).
Proof. exact (MK_COMB (@lem234524) (@lem234523 m)). Qed.
Lemma lem234526 (n : nat) (m : nat) : (term427 m n) = (term414 n m).
Proof. exact (eq_refl (term427 m n)). Qed.
Lemma lem234527 (m : nat) : (term434 m) = (term425 m).
Proof. exact (fun_ext (fun n : nat => @lem234526 n m)). Qed.
Lemma lem234528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234529 (m : nat) : (term435 m) = (term436 m).
Proof. exact (MK_COMB (@lem234528) (@lem234527 m)). Qed.
Lemma lem234530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem234531 (m : nat) : (term437 m) = (term438 m).
Proof. exact (MK_COMB (@lem234530) (@lem234529 m)). Qed.
Lemma lem234532 (n : nat) (m : nat) : (term429 m n) = (term411 n m).
Proof. exact (eq_refl (term429 m n)). Qed.
Lemma lem234533 (m : nat) : (term439 m) = (term426 m).
Proof. exact (fun_ext (fun n : nat => @lem234532 n m)). Qed.
Lemma lem234534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234535 (m : nat) : (term440 m) = (term441 m).
Proof. exact (MK_COMB (@lem234534) (@lem234533 m)). Qed.
Lemma lem234536 (m : nat) : (term424 m) = (term442 m).
Proof. exact (MK_COMB (@lem234531 m) (@lem234535 m)). Qed.
Lemma lem234537 (m : nat) : ((term423 m) = (term424 m)) = ((term420 m) = (term442 m)).
Proof. exact (MK_COMB (@lem234525 m) (@lem234536 m)). Qed.
Lemma lem234538 (m : nat) : (term420 m) = (term442 m).
Proof. exact (EQ_MP (@lem234537 m) (@lem234515 m)). Qed.
Lemma lem234643 : term421 = term443.
Proof. exact (fun_ext (fun m : nat => @lem234538 m)). Qed.
Lemma lem234644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234645 : term422 = term444.
Proof. exact (MK_COMB (@lem234644) (@lem234643)). Qed.
Lemma lem234647 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem234648 (P : nat -> Prop) (Q : nat -> Prop) : (term176 P Q) = (term177 P Q).
Proof. exact (@lem234647 nat P Q). Qed.
Lemma lem234649 : term445 = term446.
Proof. exact (@lem234648 term447 term448). Qed.
Lemma lem234650 (m : nat) : (term449 m) = (term436 m).
Proof. exact (eq_refl (term449 m)). Qed.
Lemma lem234651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem234652 (m : nat) : (term450 m) = (term438 m).
Proof. exact (MK_COMB (@lem234651) (@lem234650 m)). Qed.
Lemma lem234653 (m : nat) : (term451 m) = (term441 m).
Proof. exact (eq_refl (term451 m)). Qed.
Lemma lem234654 (m : nat) : (term452 m) = (term442 m).
Proof. exact (MK_COMB (@lem234652 m) (@lem234653 m)). Qed.
Lemma lem234655 : term453 = term443.
Proof. exact (fun_ext (fun m : nat => @lem234654 m)). Qed.
Lemma lem234656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234657 : term445 = term444.
Proof. exact (MK_COMB (@lem234656) (@lem234655)). Qed.
Lemma lem234658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234659 : term454 = term455.
Proof. exact (MK_COMB (@lem234658) (@lem234657)). Qed.
Lemma lem234660 (m : nat) : (term449 m) = (term436 m).
Proof. exact (eq_refl (term449 m)). Qed.
Lemma lem234661 : term456 = term447.
Proof. exact (fun_ext (fun m : nat => @lem234660 m)). Qed.
Lemma lem234662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234663 : term457 = term458.
Proof. exact (MK_COMB (@lem234662) (@lem234661)). Qed.
Lemma lem234664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem234665 : term459 = term460.
Proof. exact (MK_COMB (@lem234664) (@lem234663)). Qed.
Lemma lem234666 (m : nat) : (term451 m) = (term441 m).
Proof. exact (eq_refl (term451 m)). Qed.
Lemma lem234667 : term461 = term448.
Proof. exact (fun_ext (fun m : nat => @lem234666 m)). Qed.
Lemma lem234668 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234669 : term462 = term463.
Proof. exact (MK_COMB (@lem234668) (@lem234667)). Qed.
Lemma lem234670 : term446 = term464.
Proof. exact (MK_COMB (@lem234665) (@lem234669)). Qed.
Lemma lem234671 : (term445 = term446) = (term444 = term464).
Proof. exact (MK_COMB (@lem234659) (@lem234670)). Qed.
Lemma lem234672 : term444 = term464.
Proof. exact (EQ_MP (@lem234671) (@lem234649)). Qed.
Lemma lem234785 : term422 = term464.
Proof. exact (TRANS (@lem234645) (@lem234672)). Qed.
Lemma lem234787 {A : Type'} (P : Prop) (Q : A -> Prop) : (term465 A P Q) = (term466 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem234788 (P : Prop) (Q : nat -> Prop) : (term467 P Q) = (term468 P Q).
Proof. exact (@lem234787 nat P Q). Qed.
Lemma lem234789 (n : nat) (m : nat) : (term469 n m) = (term470 n m).
Proof. exact (@lem234788 (term34 m n) (term356 n m)). Qed.
Lemma lem234790 (n : nat) (m : nat) (d : nat) : (term404 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term404 n m d)). Qed.
Lemma lem234791 (n : nat) (m : nat) : (term471 n m) = (term356 n m).
Proof. exact (fun_ext (fun d : nat => @lem234790 n m d)). Qed.
Lemma lem234792 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234793 (n : nat) (m : nat) : (term472 n m) = (term31 n m).
Proof. exact (MK_COMB (@lem234792) (@lem234791 n m)). Qed.
Lemma lem234794 (m : nat) (n : nat) : (term410 m n) = (term410 m n).
Proof. exact (eq_refl (term410 m n)). Qed.
Lemma lem234795 (n : nat) (m : nat) : (term469 n m) = (term411 n m).
Proof. exact (MK_COMB (@lem234794 m n) (@lem234793 n m)). Qed.
Lemma lem234796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234797 (n : nat) (m : nat) : (term473 n m) = (term474 n m).
Proof. exact (MK_COMB (@lem234796) (@lem234795 n m)). Qed.
Lemma lem234798 (n : nat) (m : nat) (d : nat) : (term404 n m d) = (n = (Nat.add m d)).
Proof. exact (eq_refl (term404 n m d)). Qed.
Lemma lem234799 (m : nat) (n : nat) : (term410 m n) = (term410 m n).
Proof. exact (eq_refl (term410 m n)). Qed.
Lemma lem234800 (n : nat) (m : nat) (d : nat) : (term475 n m d) = (term476 n m d).
Proof. exact (MK_COMB (@lem234799 m n) (@lem234798 n m d)). Qed.
Lemma lem234801 (n : nat) (m : nat) : (term477 n m) = (term478 n m).
Proof. exact (fun_ext (fun d : nat => @lem234800 n m d)). Qed.
Lemma lem234802 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234803 (n : nat) (m : nat) : (term470 n m) = (term479 n m).
Proof. exact (MK_COMB (@lem234802) (@lem234801 n m)). Qed.
Lemma lem234804 (n : nat) (m : nat) : ((term469 n m) = (term470 n m)) = ((term411 n m) = (term479 n m)).
Proof. exact (MK_COMB (@lem234797 n m) (@lem234803 n m)). Qed.
Lemma lem234805 (n : nat) (m : nat) : (term411 n m) = (term479 n m).
Proof. exact (EQ_MP (@lem234804 n m) (@lem234789 n m)). Qed.
Lemma lem234806 (m : nat) : (term426 m) = (term480 m).
Proof. exact (fun_ext (fun n : nat => @lem234805 n m)). Qed.
Lemma lem234807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234808 (m : nat) : (term441 m) = (term481 m).
Proof. exact (MK_COMB (@lem234807) (@lem234806 m)). Qed.
Lemma lem234810 {A B : Type'} (P : type1413 A B) : (term482 A B P) = (term483 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem234811 (P : type1605) : (term484 P) = (term485 P).
Proof. exact (@lem234810 nat nat P). Qed.
Lemma lem234812 (m : nat) : (term486 m) = (term487 m).
Proof. exact (@lem234811 (term488 m)). Qed.
Lemma lem234813 (n : nat) (m : nat) : (term489 m n) = (term478 n m).
Proof. exact (eq_refl (term489 m n)). Qed.
Lemma lem234814 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem234815 (n : nat) (m : nat) (d : nat) : (term490 m n d) = (term491 n m d).
Proof. exact (MK_COMB (@lem234813 n m) (@lem234814 d)). Qed.
Lemma lem234816 (n : nat) (m : nat) (d : nat) : (term491 n m d) = (term476 n m d).
Proof. exact (eq_refl (term491 n m d)). Qed.
Lemma lem234817 (n : nat) (m : nat) (d : nat) : (term490 m n d) = (term476 n m d).
Proof. exact (TRANS (@lem234815 n m d) (@lem234816 n m d)). Qed.
Lemma lem234818 (n : nat) (m : nat) : (term492 m n) = (term478 n m).
Proof. exact (fun_ext (fun d : nat => @lem234817 n m d)). Qed.
Lemma lem234819 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem234820 (n : nat) (m : nat) : (term493 m n) = (term479 n m).
Proof. exact (MK_COMB (@lem234819) (@lem234818 n m)). Qed.
Lemma lem234821 (m : nat) : (term494 m) = (term480 m).
Proof. exact (fun_ext (fun n : nat => @lem234820 n m)). Qed.
Lemma lem234822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234823 (m : nat) : (term486 m) = (term481 m).
Proof. exact (MK_COMB (@lem234822) (@lem234821 m)). Qed.
Lemma lem234824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234825 (m : nat) : (term495 m) = (term496 m).
Proof. exact (MK_COMB (@lem234824) (@lem234823 m)). Qed.
Lemma lem234826 (n : nat) (m : nat) : (term489 m n) = (term478 n m).
Proof. exact (eq_refl (term489 m n)). Qed.
Lemma lem234827 (d : nat -> nat) (n : nat) : (d n) = (d n).
Proof. exact (eq_refl (d n)). Qed.
Lemma lem234828 (m : nat) (d : nat -> nat) (n : nat) : (term497 m d n) = (term498 m d n).
Proof. exact (MK_COMB (@lem234826 n m) (@lem234827 d n)). Qed.
Lemma lem234829 (m : nat) (d : nat -> nat) (n : nat) : (term498 m d n) = (term499 m d n).
Proof. exact (eq_refl (term498 m d n)). Qed.
Lemma lem234830 (m : nat) (d : nat -> nat) (n : nat) : (term497 m d n) = (term499 m d n).
Proof. exact (TRANS (@lem234828 m d n) (@lem234829 m d n)). Qed.
Lemma lem234831 (m : nat) (d : nat -> nat) : (term500 m d) = (term501 m d).
Proof. exact (fun_ext (fun n : nat => @lem234830 m d n)). Qed.
Lemma lem234832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234833 (m : nat) (d : nat -> nat) : (term502 m d) = (term503 m d).
Proof. exact (MK_COMB (@lem234832) (@lem234831 m d)). Qed.
Lemma lem234834 (m : nat) : (term504 m) = (term505 m).
Proof. exact (fun_ext (fun d : nat -> nat => @lem234833 m d)). Qed.
Lemma lem234835 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem234836 (m : nat) : (term487 m) = (term506 m).
Proof. exact (MK_COMB (@lem234835) (@lem234834 m)). Qed.
Lemma lem234837 (m : nat) : ((term486 m) = (term487 m)) = ((term481 m) = (term506 m)).
Proof. exact (MK_COMB (@lem234825 m) (@lem234836 m)). Qed.
Lemma lem234838 (m : nat) : (term481 m) = (term506 m).
Proof. exact (EQ_MP (@lem234837 m) (@lem234812 m)). Qed.
Lemma lem234839 (m : nat) : (term441 m) = (term506 m).
Proof. exact (TRANS (@lem234808 m) (@lem234838 m)). Qed.
Lemma lem234840 : term448 = term507.
Proof. exact (fun_ext (fun m : nat => @lem234839 m)). Qed.
Lemma lem234841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234842 : term463 = term508.
Proof. exact (MK_COMB (@lem234841) (@lem234840)). Qed.
Lemma lem234844 {A B : Type'} (P : type1413 A B) : (term482 A B P) = (term483 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem234845 (P : type1586) : (term509 P) = (term510 P).
Proof. exact (@lem234844 nat (nat -> nat) P). Qed.
Lemma lem234846 : term511 = term512.
Proof. exact (@lem234845 term513). Qed.
Lemma lem234847 (m : nat) : (term514 m) = (term505 m).
Proof. exact (eq_refl (term514 m)). Qed.
Lemma lem234848 (d : nat -> nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem234849 (m : nat) (d : nat -> nat) : (term515 m d) = (term516 m d).
Proof. exact (MK_COMB (@lem234847 m) (@lem234848 d)). Qed.
Lemma lem234850 (m : nat) (d : nat -> nat) : (term516 m d) = (term503 m d).
Proof. exact (eq_refl (term516 m d)). Qed.
Lemma lem234851 (m : nat) (d : nat -> nat) : (term515 m d) = (term503 m d).
Proof. exact (TRANS (@lem234849 m d) (@lem234850 m d)). Qed.
Lemma lem234852 (m : nat) : (term517 m) = (term505 m).
Proof. exact (fun_ext (fun d : nat -> nat => @lem234851 m d)). Qed.
Lemma lem234853 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem234854 (m : nat) : (term518 m) = (term506 m).
Proof. exact (MK_COMB (@lem234853) (@lem234852 m)). Qed.
Lemma lem234855 : term519 = term507.
Proof. exact (fun_ext (fun m : nat => @lem234854 m)). Qed.
Lemma lem234856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234857 : term511 = term508.
Proof. exact (MK_COMB (@lem234856) (@lem234855)). Qed.
Lemma lem234858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234859 : term520 = term521.
Proof. exact (MK_COMB (@lem234858) (@lem234857)). Qed.
Lemma lem234860 (m : nat) : (term514 m) = (term505 m).
Proof. exact (eq_refl (term514 m)). Qed.
Lemma lem234861 (d : type1606) (m : nat) : (d m) = (d m).
Proof. exact (eq_refl (d m)). Qed.
Lemma lem234862 (d : type1606) (m : nat) : (term522 d m) = (term523 d m).
Proof. exact (MK_COMB (@lem234860 m) (@lem234861 d m)). Qed.
Lemma lem234863 (d : type1606) (m : nat) : (term523 d m) = (term524 d m).
Proof. exact (eq_refl (term523 d m)). Qed.
Lemma lem234864 (d : type1606) (m : nat) : (term522 d m) = (term524 d m).
Proof. exact (TRANS (@lem234862 d m) (@lem234863 d m)). Qed.
Lemma lem234865 (d : type1606) : (term525 d) = (term526 d).
Proof. exact (fun_ext (fun m : nat => @lem234864 d m)). Qed.
Lemma lem234866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234867 (d : type1606) : (term527 d) = (term528 d).
Proof. exact (MK_COMB (@lem234866) (@lem234865 d)). Qed.
Lemma lem234868 : term529 = term530.
Proof. exact (fun_ext (fun d : type1606 => @lem234867 d)). Qed.
Lemma lem234869 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem234870 : term512 = term531.
Proof. exact (MK_COMB (@lem234869) (@lem234868)). Qed.
Lemma lem234871 : (term511 = term512) = (term508 = term531).
Proof. exact (MK_COMB (@lem234859) (@lem234870)). Qed.
Lemma lem234872 : term508 = term531.
Proof. exact (EQ_MP (@lem234871) (@lem234846)). Qed.
Lemma lem234873 : term463 = term531.
Proof. exact (TRANS (@lem234842) (@lem234872)). Qed.
Lemma lem234874 : term460 = term460.
Proof. exact (eq_refl term460). Qed.
Lemma lem234875 : term464 = term532.
Proof. exact (MK_COMB (@lem234874) (@lem234873)). Qed.
Lemma lem234877 {A : Type'} (P : Prop) (Q : A -> Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem234878 (P : Prop) (Q : type961) : (term535 P Q) = (term536 P Q).
Proof. exact (@lem234877 type1606 P Q). Qed.
Lemma lem234879 : term537 = term538.
Proof. exact (@lem234878 term458 term530). Qed.
Lemma lem234880 (d : type1606) : (term539 d) = (term528 d).
Proof. exact (eq_refl (term539 d)). Qed.
Lemma lem234881 : term540 = term530.
Proof. exact (fun_ext (fun d : type1606 => @lem234880 d)). Qed.
Lemma lem234882 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem234883 : term541 = term531.
Proof. exact (MK_COMB (@lem234882) (@lem234881)). Qed.
Lemma lem234884 : term460 = term460.
Proof. exact (eq_refl term460). Qed.
Lemma lem234885 : term537 = term532.
Proof. exact (MK_COMB (@lem234884) (@lem234883)). Qed.
Lemma lem234886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem234887 : term542 = term543.
Proof. exact (MK_COMB (@lem234886) (@lem234885)). Qed.
Lemma lem234888 (d : type1606) : (term539 d) = (term528 d).
Proof. exact (eq_refl (term539 d)). Qed.
Lemma lem234889 : term460 = term460.
Proof. exact (eq_refl term460). Qed.
Lemma lem234890 (d : type1606) : (term544 d) = (term545 d).
Proof. exact (MK_COMB (@lem234889) (@lem234888 d)). Qed.
Lemma lem234891 : term546 = term547.
Proof. exact (fun_ext (fun d : type1606 => @lem234890 d)). Qed.
Lemma lem234892 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem234893 : term538 = term548.
Proof. exact (MK_COMB (@lem234892) (@lem234891)). Qed.
Lemma lem234894 : (term537 = term538) = (term532 = term548).
Proof. exact (MK_COMB (@lem234887) (@lem234893)). Qed.
Lemma lem234895 : term532 = term548.
Proof. exact (EQ_MP (@lem234894) (@lem234879)). Qed.
Lemma lem234896 : term464 = term548.
Proof. exact (TRANS (@lem234875) (@lem234895)). Qed.
Lemma lem234897 : term422 = term548.
Proof. exact (TRANS (@lem234785) (@lem234896)). Qed.
Lemma lem234898 : term400 = term548.
Proof. exact (TRANS (@lem234507) (@lem234897)). Qed.
Lemma lem234899 (h1 : term400) : term548.
Proof. exact (EQ_MP (@lem234898) (@lem234440 h1)). Qed.
Lemma lem234904 (n : nat) (m : nat) : (term394 n m) = (term394 n m).
Proof. exact (eq_refl (term394 n m)). Qed.
Lemma lem234905 (m : nat) : (term395 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem234904 n m)). Qed.
Lemma lem234906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234907 (m : nat) : (term396 m) = (term396 m).
Proof. exact (MK_COMB (@lem234906) (@lem234905 m)). Qed.
Lemma lem234908 : term397 = term397.
Proof. exact (fun_ext (fun m : nat => @lem234907 m)). Qed.
Lemma lem234909 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem234966 : term371 = term371.
Proof. exact (MK_COMB (@lem234909) (@lem234908)). Qed.
Lemma lem234967 (h1 : term371) : term371.
Proof. exact (EQ_MP (@lem234966) (@lem234441 h1)). Qed.
Lemma lem234968 (d : type1606) (h1 : term545 d) : term545 d.
Proof. exact (h1). Qed.
Lemma lem234986 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem234997 (m : nat) (n : nat) (d : nat) : (term406 m n d) = (term406 m n d).
Proof. exact (eq_refl (term406 m n d)). Qed.
Lemma lem234998 (m : nat) (n : nat) : (term408 m n) = (term408 m n).
Proof. exact (fun_ext (fun d : nat => @lem234997 m n d)). Qed.
Lemma lem234999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235000 (m : nat) (n : nat) : (term409 m n) = (term409 m n).
Proof. exact (MK_COMB (@lem234999) (@lem234998 m n)). Qed.
Lemma lem235001 (m : nat) (n : nat) (h1 : term364 m n) : term409 m n.
Proof. exact (EQ_MP (@lem235000 m n) (@lem234473 m n h1)). Qed.
Lemma lem235014 (n : nat) (m : nat) : (term394 n m) = (term394 n m).
Proof. exact (eq_refl (term394 n m)). Qed.
Lemma lem235015 (m : nat) : (term395 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem235014 n m)). Qed.
Lemma lem235016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235017 (m : nat) : (term396 m) = (term396 m).
Proof. exact (MK_COMB (@lem235016) (@lem235015 m)). Qed.
Lemma lem235018 : term397 = term397.
Proof. exact (fun_ext (fun m : nat => @lem235017 m)). Qed.
Lemma lem235019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235020 : term371 = term371.
Proof. exact (MK_COMB (@lem235019) (@lem235018)). Qed.
Lemma lem235021 (h1 : term371) : term371.
Proof. exact (EQ_MP (@lem235020) (@lem234967 h1)). Qed.
Lemma lem235044 (d : type1606) (m : nat) (n : nat) : (term549 d m n) = (term549 d m n).
Proof. exact (eq_refl (term549 d m n)). Qed.
Lemma lem235045 (d : type1606) (m : nat) : (term550 d m) = (term550 d m).
Proof. exact (fun_ext (fun n : nat => @lem235044 d m n)). Qed.
Lemma lem235046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235047 (d : type1606) (m : nat) : (term524 d m) = (term524 d m).
Proof. exact (MK_COMB (@lem235046) (@lem235045 d m)). Qed.
Lemma lem235048 (d : type1606) : (term526 d) = (term526 d).
Proof. exact (fun_ext (fun m : nat => @lem235047 d m)). Qed.
Lemma lem235049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235050 (d : type1606) : (term528 d) = (term528 d).
Proof. exact (MK_COMB (@lem235049) (@lem235048 d)). Qed.
Lemma lem235061 (n : nat) (m : nat) (d : nat) : (term406 n m d) = (term406 n m d).
Proof. exact (eq_refl (term406 n m d)). Qed.
Lemma lem235062 (n : nat) (m : nat) : (term408 n m) = (term408 n m).
Proof. exact (fun_ext (fun d : nat => @lem235061 n m d)). Qed.
Lemma lem235063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235064 (n : nat) (m : nat) : (term409 n m) = (term409 n m).
Proof. exact (MK_COMB (@lem235063) (@lem235062 n m)). Qed.
Lemma lem235071 (m : nat) (n : nat) : (term412 m n) = (term412 m n).
Proof. exact (eq_refl (term412 m n)). Qed.
Lemma lem235072 (n : nat) (m : nat) : (term414 n m) = (term414 n m).
Proof. exact (MK_COMB (@lem235071 m n) (@lem235064 n m)). Qed.
Lemma lem235073 (m : nat) : (term425 m) = (term425 m).
Proof. exact (fun_ext (fun n : nat => @lem235072 n m)). Qed.
Lemma lem235074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235075 (m : nat) : (term436 m) = (term436 m).
Proof. exact (MK_COMB (@lem235074) (@lem235073 m)). Qed.
Lemma lem235076 : term447 = term447.
Proof. exact (fun_ext (fun m : nat => @lem235075 m)). Qed.
Lemma lem235077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235078 : term458 = term458.
Proof. exact (MK_COMB (@lem235077) (@lem235076)). Qed.
Lemma lem235079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem235080 : term460 = term460.
Proof. exact (MK_COMB (@lem235079) (@lem235078)). Qed.
Lemma lem235081 (d : type1606) : (term545 d) = (term545 d).
Proof. exact (MK_COMB (@lem235080) (@lem235050 d)). Qed.
Lemma lem235082 (d : type1606) (h1 : term545 d) : term545 d.
Proof. exact (EQ_MP (@lem235081 d) (@lem234968 d h1)). Qed.
Lemma lem235083 (d : type1606) (h1 : term545 d) : term528 d.
Proof. exact (proj2 (@lem235082 d h1)). Qed.
Lemma lem235092 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem235094 (m : nat) (n : nat) (d : nat) : (term406 m n d) = (term406 m n d).
Proof. exact (eq_refl (term406 m n d)). Qed.
Lemma lem235095 (m : nat) (n : nat) : (term408 m n) = (term408 m n).
Proof. exact (fun_ext (fun d : nat => @lem235094 m n d)). Qed.
Lemma lem235096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235098 (m : nat) (n : nat) : (term409 m n) = (term409 m n).
Proof. exact (MK_COMB (@lem235096) (@lem235095 m n)). Qed.
Lemma lem235099 (m : nat) (n : nat) (h1 : term364 m n) : term409 m n.
Proof. exact (EQ_MP (@lem235098 m n) (@lem235001 m n h1)). Qed.
Lemma lem235107 (n : nat) (m : nat) : (term394 n m) = (term394 n m).
Proof. exact (eq_refl (term394 n m)). Qed.
Lemma lem235108 (m : nat) : (term395 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem235107 n m)). Qed.
Lemma lem235109 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235110 (m : nat) : (term396 m) = (term396 m).
Proof. exact (MK_COMB (@lem235109) (@lem235108 m)). Qed.
Lemma lem235111 : term397 = term397.
Proof. exact (fun_ext (fun m : nat => @lem235110 m)). Qed.
Lemma lem235112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235114 : term371 = term371.
Proof. exact (MK_COMB (@lem235112) (@lem235111)). Qed.
Lemma lem235115 (h1 : term371) : term371.
Proof. exact (EQ_MP (@lem235114) (@lem235021 h1)). Qed.
Lemma lem235167 (d : type1606) (m : nat) (n : nat) : (term549 d m n) = (term549 d m n).
Proof. exact (eq_refl (term549 d m n)). Qed.
Lemma lem235168 (d : type1606) (m : nat) : (term550 d m) = (term550 d m).
Proof. exact (fun_ext (fun n : nat => @lem235167 d m n)). Qed.
Lemma lem235169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235170 (d : type1606) (m : nat) : (term524 d m) = (term524 d m).
Proof. exact (MK_COMB (@lem235169) (@lem235168 d m)). Qed.
Lemma lem235171 (d : type1606) : (term526 d) = (term526 d).
Proof. exact (fun_ext (fun m : nat => @lem235170 d m)). Qed.
Lemma lem235172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem235174 (d : type1606) : (term528 d) = (term528 d).
Proof. exact (MK_COMB (@lem235172) (@lem235171 d)). Qed.
Lemma lem235175 (d : type1606) (h1 : term545 d) : term528 d.
Proof. exact (EQ_MP (@lem235174 d) (@lem235083 d h1)). Qed.
Lemma lem235176 (_4636 : nat) (m : nat) (n : nat) (h1 : term364 m n) : term551 m n _4636.
Proof. exact (@lem235099 m n h1 _4636). Qed.
Lemma lem235177 (m : nat) (n : nat) (_4636 : nat) : (term551 m n _4636) = (term406 m n _4636).
Proof. exact (eq_refl (term551 m n _4636)). Qed.
Lemma lem235179 (_4637 : nat) (h1 : term371) : term552 _4637.
Proof. exact (@lem235115 h1 _4637). Qed.
Lemma lem235180 (_4637 : nat) : (term552 _4637) = (term396 _4637).
Proof. exact (eq_refl (term552 _4637)). Qed.
Lemma lem235181 (_4637 : nat) (h1 : term371) : term396 _4637.
Proof. exact (EQ_MP (@lem235180 _4637) (@lem235179 _4637 h1)). Qed.
Lemma lem235182 (_4637 : nat) (_4638 : nat) (h1 : term371) : term553 _4637 _4638.
Proof. exact (@lem235181 _4637 h1 _4638). Qed.
Lemma lem235183 (_4638 : nat) (_4637 : nat) : (term553 _4637 _4638) = (term394 _4638 _4637).
Proof. exact (eq_refl (term553 _4637 _4638)). Qed.
Lemma lem235194 (_4642 : nat) (d : type1606) (h1 : term545 d) : term554 d _4642.
Proof. exact (@lem235175 d h1 _4642). Qed.
Lemma lem235195 (d : type1606) (_4642 : nat) : (term554 d _4642) = (term524 d _4642).
Proof. exact (eq_refl (term554 d _4642)). Qed.
Lemma lem235196 (_4642 : nat) (d : type1606) (h1 : term545 d) : term524 d _4642.
Proof. exact (EQ_MP (@lem235195 d _4642) (@lem235194 _4642 d h1)). Qed.
Lemma lem235197 (_4642 : nat) (_4643 : nat) (d : type1606) (h1 : term545 d) : term555 d _4642 _4643.
Proof. exact (@lem235196 _4642 d h1 _4643). Qed.
Lemma lem235198 (d : type1606) (_4642 : nat) (_4643 : nat) : (term555 d _4642 _4643) = (term549 d _4642 _4643).
Proof. exact (eq_refl (term555 d _4642 _4643)). Qed.
Lemma lem235203 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem235205 (_4636 : nat) (m : nat) (n : nat) (h1 : term364 m n) : term406 m n _4636.
Proof. exact (EQ_MP (@lem235177 m n _4636) (@lem235176 _4636 m n h1)). Qed.
Lemma lem235211 (_4638 : nat) (_4637 : nat) (h1 : term371) : term394 _4638 _4637.
Proof. exact (EQ_MP (@lem235183 _4638 _4637) (@lem235182 _4637 _4638 h1)). Qed.
Lemma lem235223 (_4642 : nat) (_4643 : nat) (d : type1606) (h1 : term545 d) : term549 d _4642 _4643.
Proof. exact (EQ_MP (@lem235198 d _4642 _4643) (@lem235197 _4642 _4643 d h1)). Qed.
Lemma lem235284 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (h1). Qed.
Lemma lem235285 (m : nat) (n : nat) (h1 : term34 m n) : term556 m n.
Proof. exact (fun h0 : Peano.le m n => @lem235284 m n h1). Qed.
Lemma lem235287 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem235288 (m : nat) (n : nat) : (term556 m n) = (term34 m n).
Proof. exact (@lem235287 (Peano.le m n)). Qed.
Lemma lem235289 (m : nat) (n : nat) (h1 : term34 m n) : term34 m n.
Proof. exact (EQ_MP (@lem235288 m n) (@lem235285 m n h1)). Qed.
Lemma lem235300 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem235301 (_4638 : nat) (_4637 : nat) : (term394 _4637 _4638) = (term394 _4638 _4637).
Proof. exact (@lem235300 (Peano.le _4637 _4638) (Peano.le _4638 _4637)). Qed.
Lemma lem235307 (_4638 : nat) (_4637 : nat) : (term558 _4638 _4637) = (term558 _4638 _4637).
Proof. exact (eq_refl (term558 _4638 _4637)). Qed.
Lemma lem235308 (_4638 : nat) (_4637 : nat) : ((term394 _4638 _4637) = (term394 _4637 _4638)) = ((term394 _4638 _4637) = (term394 _4638 _4637)).
Proof. exact (MK_COMB (@lem235307 _4638 _4637) (@lem235301 _4638 _4637)). Qed.
Lemma lem235310 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem235311 (x : Prop) : (x = x) = True.
Proof. exact (@lem235310 Prop x). Qed.
Lemma lem235312 (_4638 : nat) (_4637 : nat) : ((term394 _4638 _4637) = (term394 _4638 _4637)) = True.
Proof. exact (@lem235311 (term394 _4638 _4637)). Qed.
Lemma lem235313 (_4637 : nat) (_4638 : nat) : ((term394 _4638 _4637) = (term394 _4637 _4638)) = True.
Proof. exact (TRANS (@lem235308 _4638 _4637) (@lem235312 _4638 _4637)). Qed.
Lemma lem235314 (_4637 : nat) (_4638 : nat) : True = ((term394 _4638 _4637) = (term394 _4637 _4638)).
Proof. exact (SYM (@lem235313 _4637 _4638)). Qed.
Lemma lem235315 (_4637 : nat) (_4638 : nat) : (term394 _4638 _4637) = (term394 _4637 _4638).
Proof. exact (EQ_MP (@lem235314 _4637 _4638) (@lem0)). Qed.
Lemma lem235316 (_4637 : nat) (_4638 : nat) (h1 : term371) : term394 _4637 _4638.
Proof. exact (EQ_MP (@lem235315 _4637 _4638) (@lem235211 _4638 _4637 h1)). Qed.
Lemma lem235318 (b : Prop) (a : Prop) : (a \/ b) = (term256 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem235321 (_4638 : nat) (_4637 : nat) : (term394 _4637 _4638) = (term559 _4638 _4637).
Proof. exact (@lem235318 (Peano.le _4637 _4638) (Peano.le _4638 _4637)). Qed.
Lemma lem235324 (_4638 : nat) (_4637 : nat) (h1 : term371) : term559 _4638 _4637.
Proof. exact (EQ_MP (@lem235321 _4638 _4637) (@lem235316 _4637 _4638 h1)). Qed.
Lemma lem235325 (n : nat) (m : nat) (h1 : term371) : term559 n m.
Proof. exact (@lem235324 n m h1). Qed.
Lemma lem235328 (m : nat) (n : nat) (h1 : term371) (h2 : term34 m n) : Peano.le n m.
Proof. exact (@lem235325 n m h1 (@lem235289 m n h2)). Qed.
Lemma lem235329 (m : nat) (n : nat) (h1 : term371) (h2 : term34 m n) : term560 n m.
Proof. exact (fun h0 : term34 n m => @lem235328 m n h1 h2). Qed.
Lemma lem235331 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem235332 (n : nat) (m : nat) : (term560 n m) = (Peano.le n m).
Proof. exact (@lem235331 (Peano.le n m)). Qed.
Lemma lem235333 (m : nat) (n : nat) (h1 : term371) (h2 : term34 m n) : Peano.le n m.
Proof. exact (EQ_MP (@lem235332 n m) (@lem235329 m n h1 h2)). Qed.
Lemma lem235339 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem235340 (d : type1606) (_4642 : nat) (_4643 : nat) : (term549 d _4642 _4643) = (term561 d _4642 _4643).
Proof. exact (@lem235339 (_4643 = (term562 d _4642 _4643)) (term34 _4642 _4643)). Qed.
Lemma lem235348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem235349 (d : type1606) (_4642 : nat) (_4643 : nat) : (term563 d _4642 _4643) = (term564 d _4642 _4643).
Proof. exact (MK_COMB (@lem235348) (@lem235340 d _4642 _4643)). Qed.
Lemma lem235357 (d : type1606) (_4642 : nat) (_4643 : nat) : (term561 d _4642 _4643) = (term561 d _4642 _4643).
Proof. exact (eq_refl (term561 d _4642 _4643)). Qed.
Lemma lem235358 (d : type1606) (_4642 : nat) (_4643 : nat) : ((term549 d _4642 _4643) = (term561 d _4642 _4643)) = ((term561 d _4642 _4643) = (term561 d _4642 _4643)).
Proof. exact (MK_COMB (@lem235349 d _4642 _4643) (@lem235357 d _4642 _4643)). Qed.
Lemma lem235360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem235361 (x : Prop) : (x = x) = True.
Proof. exact (@lem235360 Prop x). Qed.
Lemma lem235362 (d : type1606) (_4642 : nat) (_4643 : nat) : ((term561 d _4642 _4643) = (term561 d _4642 _4643)) = True.
Proof. exact (@lem235361 (term561 d _4642 _4643)). Qed.
Lemma lem235363 (d : type1606) (_4642 : nat) (_4643 : nat) : ((term549 d _4642 _4643) = (term561 d _4642 _4643)) = True.
Proof. exact (TRANS (@lem235358 d _4642 _4643) (@lem235362 d _4642 _4643)). Qed.
Lemma lem235364 (d : type1606) (_4642 : nat) (_4643 : nat) : True = ((term549 d _4642 _4643) = (term561 d _4642 _4643)).
Proof. exact (SYM (@lem235363 d _4642 _4643)). Qed.
Lemma lem235365 (d : type1606) (_4642 : nat) (_4643 : nat) : (term549 d _4642 _4643) = (term561 d _4642 _4643).
Proof. exact (EQ_MP (@lem235364 d _4642 _4643) (@lem0)). Qed.
Lemma lem235366 (_4642 : nat) (_4643 : nat) (d : type1606) (h1 : term545 d) : term561 d _4642 _4643.
Proof. exact (EQ_MP (@lem235365 d _4642 _4643) (@lem235223 _4642 _4643 d h1)). Qed.
Lemma lem235368 (b : Prop) (a : Prop) : (a \/ b) = (term256 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem235369 (d : type1606) (_4642 : nat) (_4643 : nat) : (term561 d _4642 _4643) = (term565 d _4642 _4643).
Proof. exact (@lem235368 (term34 _4642 _4643) (_4643 = (term562 d _4642 _4643))). Qed.
Lemma lem235371 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem235372 (_4642 : nat) (_4643 : nat) : (term566 _4642 _4643) = (Peano.le _4642 _4643).
Proof. exact (@lem235371 (Peano.le _4642 _4643)). Qed.
Lemma lem235373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem235374 (_4642 : nat) (_4643 : nat) : (term567 _4642 _4643) = (term123 _4642 _4643).
Proof. exact (MK_COMB (@lem235373) (@lem235372 _4642 _4643)). Qed.
Lemma lem235375 (d : type1606) (_4642 : nat) (_4643 : nat) : (_4643 = (term562 d _4642 _4643)) = (_4643 = (term562 d _4642 _4643)).
Proof. exact (eq_refl (_4643 = (term562 d _4642 _4643))). Qed.
Lemma lem235376 (d : type1606) (_4642 : nat) (_4643 : nat) : (term565 d _4642 _4643) = (term568 d _4642 _4643).
Proof. exact (MK_COMB (@lem235374 _4642 _4643) (@lem235375 d _4642 _4643)). Qed.
Lemma lem235377 (d : type1606) (_4642 : nat) (_4643 : nat) : (term561 d _4642 _4643) = (term568 d _4642 _4643).
Proof. exact (TRANS (@lem235369 d _4642 _4643) (@lem235376 d _4642 _4643)). Qed.
Lemma lem235380 (_4642 : nat) (_4643 : nat) (d : type1606) (h1 : term545 d) : term568 d _4642 _4643.
Proof. exact (EQ_MP (@lem235377 d _4642 _4643) (@lem235366 _4642 _4643 d h1)). Qed.
Lemma lem235381 (n : nat) (m : nat) (d : type1606) (h1 : term545 d) : term568 d n m.
Proof. exact (@lem235380 n m d h1). Qed.
Lemma lem235384 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term34 m n) (h3 : term545 d) : m = (term562 d n m).
Proof. exact (@lem235381 n m d h3 (@lem235333 m n h1 h2)). Qed.
Lemma lem235385 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term34 m n) (h3 : term545 d) : term569 d n m.
Proof. exact (fun h0 : term570 d n m => @lem235384 m n d h1 h2 h3). Qed.
Lemma lem235387 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem235388 (d : type1606) (n : nat) (m : nat) : (term569 d n m) = (m = (term562 d n m)).
Proof. exact (@lem235387 (m = (term562 d n m))). Qed.
Lemma lem235389 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term34 m n) (h3 : term545 d) : m = (term562 d n m).
Proof. exact (EQ_MP (@lem235388 d n m) (@lem235385 m n d h1 h2 h3)). Qed.
Lemma lem235392 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem235394 (m : nat) (n : nat) (_4636 : nat) : (term406 m n _4636) = (term571 m n _4636).
Proof. exact (@lem235392 (m = (Nat.add n _4636))). Qed.
Lemma lem235397 (_4636 : nat) (m : nat) (n : nat) (h1 : term364 m n) : term571 m n _4636.
Proof. exact (EQ_MP (@lem235394 m n _4636) (@lem235205 _4636 m n h1)). Qed.
Lemma lem235398 (d : type1606) (m : nat) (n : nat) (h1 : term364 m n) : term572 d n m.
Proof. exact (@lem235397 (d n m) m n h1). Qed.
Lemma lem235401 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (@lem235398 d m n h2 (@lem235389 m n d h1 h3 h4)). Qed.
Lemma lem235402 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : term265.
Proof. exact (fun h0 : ~ False => @lem235401 m n d h1 h2 h3 h4). Qed.
Lemma lem235404 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem235405 : term265 = False.
Proof. exact (@lem235404 False). Qed.
Lemma lem235406 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235405) (@lem235402 m n d h1 h2 h3 h4)). Qed.
Lemma lem235407 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : (term34 m n) = False.
Proof. exact (prop_ext (fun h5 : term34 m n => @lem235406 m n d h1 h2 h3 h4) (fun h5 : False => @lem235203 m n h3)). Qed.
Lemma lem235408 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235407 m n d h1 h2 h3 h4) (@lem235203 m n h3)). Qed.
Lemma lem235409 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : (term34 m n) = False.
Proof. exact (prop_ext (fun h5 : term34 m n => @lem235408 m n d h1 h2 h3 h4) (fun h5 : False => @lem235092 m n h3)). Qed.
Lemma lem235410 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235409 m n d h1 h2 h3 h4) (@lem235092 m n h3)). Qed.
Lemma lem235411 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : term371 = False.
Proof. exact (prop_ext (fun h5 : term371 => @lem235410 m n d h1 h2 h3 h4) (fun h5 : False => @lem235115 h1)). Qed.
Lemma lem235412 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235411 m n d h1 h2 h3 h4) (@lem235115 h1)). Qed.
Lemma lem235413 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : (term34 m n) = False.
Proof. exact (prop_ext (fun h5 : term34 m n => @lem235412 m n d h1 h2 h3 h4) (fun h5 : False => @lem235092 m n h3)). Qed.
Lemma lem235414 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235413 m n d h1 h2 h3 h4) (@lem235092 m n h3)). Qed.
Lemma lem235415 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : (term545 d) = False.
Proof. exact (prop_ext (fun h5 : term545 d => @lem235414 m n d h1 h2 h3 h4) (fun h5 : False => @lem235082 d h4)). Qed.
Lemma lem235416 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235415 m n d h1 h2 h3 h4) (@lem235082 d h4)). Qed.
Lemma lem235417 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : term371 = False.
Proof. exact (prop_ext (fun h5 : term371 => @lem235416 m n d h1 h2 h3 h4) (fun h5 : False => @lem235021 h1)). Qed.
Lemma lem235418 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235417 m n d h1 h2 h3 h4) (@lem235021 h1)). Qed.
Lemma lem235419 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : (term34 m n) = False.
Proof. exact (prop_ext (fun h5 : term34 m n => @lem235418 m n d h1 h2 h3 h4) (fun h5 : False => @lem234986 m n h3)). Qed.
Lemma lem235420 (m : nat) (n : nat) (d : type1606) (h1 : term371) (h2 : term364 m n) (h3 : term34 m n) (h4 : term545 d) : False.
Proof. exact (EQ_MP (@lem235419 m n d h1 h2 h3 h4) (@lem234986 m n h3)). Qed.
Lemma lem235421 (m : nat) (n : nat) (h1 : term400) (h2 : term371) (h3 : term364 m n) (h4 : term34 m n) : False.
Proof. exact (ex_elim (@lem234899 h1) (fun d : type1606 => fun h0 : term547 d => @lem235420 m n d h2 h3 h4 h0)). Qed.
Lemma lem235422 (m : nat) (n : nat) (h1 : term400) (h2 : term371) (h3 : term364 m n) (h4 : term34 m n) : term371 = False.
Proof. exact (prop_ext (fun h5 : term371 => @lem235421 m n h1 h2 h3 h4) (fun h5 : False => @lem234967 h2)). Qed.
Lemma lem235423 (m : nat) (n : nat) (h1 : term400) (h2 : term371) (h3 : term364 m n) (h4 : term34 m n) : False.
Proof. exact (EQ_MP (@lem235422 m n h1 h2 h3 h4) (@lem234967 h2)). Qed.
Lemma lem235424 (m : nat) (n : nat) (h1 : term400) (h2 : term371) (h3 : term364 m n) (h4 : term34 m n) : (term34 m n) = False.
Proof. exact (prop_ext (fun h5 : term34 m n => @lem235423 m n h1 h2 h3 h4) (fun h5 : False => @lem234453 m n h4)). Qed.
Lemma lem235425 (m : nat) (n : nat) (h1 : term400) (h2 : term371) (h3 : term364 m n) (h4 : term34 m n) : False.
Proof. exact (EQ_MP (@lem235424 m n h1 h2 h3 h4) (@lem234453 m n h4)). Qed.
Lemma lem235426 (m : nat) (n : nat) (h1 : term400) (h2 : term364 m n) (h3 : term34 m n) : term369.
Proof. exact (fun h0 : term371 => @lem235425 m n h1 h0 h2 h3). Qed.
Lemma lem235427 : term369 = term370.
Proof. exact (@lem69 term371). Qed.
Lemma lem235428 (m : nat) (n : nat) (h1 : term400) (h2 : term364 m n) (h3 : term34 m n) : term370.
Proof. exact (EQ_MP (@lem235427) (@lem235426 m n h1 h2 h3)). Qed.
Lemma lem235429 (m : nat) (n : nat) (h1 : term364 m n) (h2 : term34 m n) : term374.
Proof. exact (fun h0 : term400 => @lem235428 m n h0 h1 h2). Qed.
Lemma lem235430 (m : nat) (n : nat) (h1 : term34 m n) : term377 m n.
Proof. exact (fun h0 : term364 m n => @lem235429 m n h0 h1). Qed.
Lemma lem235431 (m : nat) (n : nat) : term380 m n.
Proof. exact (fun h0 : term34 m n => @lem235430 m n h0). Qed.
Lemma lem235432 (p : nat) (m : nat) (n : nat) : term381 p m n.
Proof. exact (fun h0 : term41 p => @lem235431 m n). Qed.
Lemma lem235437 (m : nat) (n : nat) : term385 m n.
Proof. exact (fun p : nat => @lem235432 p m n). Qed.
Lemma lem235442 (n : nat) : term389 n.
Proof. exact (fun m : nat => @lem235437 m n). Qed.
Lemma lem235447 : term393.
Proof. exact (fun n : nat => @lem235442 n). Qed.
Lemma lem235448 : term392.
Proof. exact (EQ_MP (@lem234436) (@lem235447)). Qed.
Lemma lem235449 (n : nat) : term573 n.
Proof. exact (@lem235448 n). Qed.
Lemma lem235450 (n : nat) : (term573 n) = (term388 n).
Proof. exact (eq_refl (term573 n)). Qed.
Lemma lem235451 (n : nat) : term388 n.
Proof. exact (EQ_MP (@lem235450 n) (@lem235449 n)). Qed.
Lemma lem235452 (n : nat) (m : nat) : term574 n m.
Proof. exact (@lem235451 n m). Qed.
Lemma lem235453 (m : nat) (n : nat) : (term574 n m) = (term384 m n).
Proof. exact (eq_refl (term574 n m)). Qed.
Lemma lem235454 (m : nat) (n : nat) : term384 m n.
Proof. exact (EQ_MP (@lem235453 m n) (@lem235452 n m)). Qed.
Lemma lem235455 (m : nat) (n : nat) (p : nat) : term575 m n p.
Proof. exact (@lem235454 m n p). Qed.
Lemma lem235456 (p : nat) (m : nat) (n : nat) : (term575 m n p) = (term365 p m n).
Proof. exact (eq_refl (term575 m n p)). Qed.
Lemma lem235457 (p : nat) (m : nat) (n : nat) : term365 p m n.
Proof. exact (EQ_MP (@lem235456 p m n) (@lem235455 m n p)). Qed.
Lemma lem235459 (p : nat) (m : nat) (n : nat) : term365 p m n.
Proof. exact (@lem234174 p m n (@lem235457 p m n)). Qed.
Lemma lem235460 (m : nat) (n : nat) (p : nat) (h1 : term41 p) : term379 m n.
Proof. exact (@lem235459 p m n (@lem231449 p h1)). Qed.
Lemma lem235461 (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : term376 m n.
Proof. exact (@lem235460 m n p h2 (@lem231418 m n h1)). Qed.
Lemma lem235462 (m : nat) (n : nat) (p : nat) (h1 : term364 m n) (h2 : term34 m n) (h3 : term41 p) : term373.
Proof. exact (@lem235461 m n p h2 h3 (@lem234159 m n h1)). Qed.
Lemma lem235463 (m : nat) (n : nat) (p : nat) (h1 : term364 m n) (h2 : term34 m n) (h3 : term41 p) : term369.
Proof. exact (@lem235462 m n p h1 h2 h3 (@lem99708)). Qed.
Lemma lem235464 (m : nat) (n : nat) (p : nat) (h1 : term364 m n) (h2 : term34 m n) (h3 : term41 p) : False.
Proof. exact (@lem235463 m n p h1 h2 h3 (@lem96155)). Qed.
Lemma lem235465 (m : nat) (n : nat) (p : nat) (h1 : term364 m n) (h2 : term34 m n) (h3 : term41 p) : (term364 m n) = False.
Proof. exact (prop_ext (fun h4 : term364 m n => @lem235464 m n p h1 h2 h3) (fun h4 : False => @lem234159 m n h1)). Qed.
Lemma lem235466 (m : nat) (n : nat) (p : nat) (h1 : term364 m n) (h2 : term34 m n) (h3 : term41 p) : False.
Proof. exact (EQ_MP (@lem235465 m n p h1 h2 h3) (@lem234159 m n h1)). Qed.
Lemma lem235467 (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : term363 m n.
Proof. exact (fun h0 : term364 m n => @lem235466 m n p h0 h1 h2). Qed.
Lemma lem235468 (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : term31 m n.
Proof. exact (EQ_MP (@lem234158 m n) (@lem235467 m n p h1 h2)). Qed.
Lemma lem235481 (m : nat) : term576 m.
Proof. exact (@lem182819 m). Qed.
Lemma lem235482 (m : nat) : (term576 m) = (term577 m).
Proof. exact (eq_refl (term576 m)). Qed.
Lemma lem235483 (m : nat) : term577 m.
Proof. exact (EQ_MP (@lem235482 m) (@lem235481 m)). Qed.
Lemma lem235484 (m : nat) (n : nat) : term578 m n.
Proof. exact (@lem235483 m n). Qed.
Lemma lem235485 (m : nat) (n : nat) : (term578 m n) = (term579 m n).
Proof. exact (eq_refl (term578 m n)). Qed.
Lemma lem235486 (m : nat) (n : nat) : term579 m n.
Proof. exact (EQ_MP (@lem235485 m n) (@lem235484 m n)). Qed.
Lemma lem235487 (m : nat) (n : nat) (p : nat) : term580 m n p.
Proof. exact (@lem235486 m n p). Qed.
Lemma lem235488 (p : nat) (m : nat) (n : nat) : (term580 m n p) = ((term581 m p n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term580 m n p)). Qed.
Lemma lem235490 (m : nat) : term582 m.
Proof. exact (@lem87724 m). Qed.
Lemma lem235491 (m : nat) : (term582 m) = (term583 m).
Proof. exact (eq_refl (term582 m)). Qed.
Lemma lem235492 (m : nat) : term583 m.
Proof. exact (EQ_MP (@lem235491 m) (@lem235490 m)). Qed.
Lemma lem235493 (m : nat) (n : nat) : term584 m n.
Proof. exact (@lem235492 m n). Qed.
Lemma lem235494 (n : nat) (m : nat) : (term584 m n) = (term585 n m).
Proof. exact (eq_refl (term584 m n)). Qed.
Lemma lem235495 (n : nat) (m : nat) : term585 n m.
Proof. exact (EQ_MP (@lem235494 n m) (@lem235493 m n)). Qed.
Lemma lem235496 (n : nat) (m : nat) (p : nat) : term586 n m p.
Proof. exact (@lem235495 n m p). Qed.
Lemma lem235497 (n : nat) (m : nat) (p : nat) : (term586 n m p) = ((term279 m n p) = (term587 n m p)).
Proof. exact (eq_refl (term586 n m p)). Qed.
Lemma lem235517 (n : nat) (m : nat) (p : nat) : (term279 m n p) = (term587 n m p).
Proof. exact (EQ_MP (@lem235497 n m p) (@lem235496 n m p)). Qed.
Lemma lem235518 (n : nat) (p : nat) (d : nat) : (term279 p n d) = (term587 n p d).
Proof. exact (@lem235517 n p d). Qed.
Lemma lem235519 (x : nat) : (Nat.modulo x) = (Nat.modulo x).
Proof. exact (eq_refl (Nat.modulo x)). Qed.
Lemma lem235520 (x : nat) (n : nat) (p : nat) (d : nat) : (term588 x p n d) = (term589 x n p d).
Proof. exact (MK_COMB (@lem235519 x) (@lem235518 n p d)). Qed.
Lemma lem235521 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem235522 (x : nat) (n : nat) (p : nat) (d : nat) : (term590 x p n d) = (term591 x n p d).
Proof. exact (MK_COMB (@lem235521) (@lem235520 x n p d)). Qed.
Lemma lem235523 (p : nat) (n : nat) : (Nat.pow p n) = (Nat.pow p n).
Proof. exact (eq_refl (Nat.pow p n)). Qed.
Lemma lem235524 (x : nat) (d : nat) (p : nat) (n : nat) : (term360 x d p n) = (term592 x d p n).
Proof. exact (MK_COMB (@lem235522 x n p d) (@lem235523 p n)). Qed.
Lemma lem235526 (p : nat) (m : nat) (n : nat) : (term581 m p n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem235488 p m n) (@lem235487 m n p)). Qed.
Lemma lem235527 (d : nat) (x : nat) (p : nat) (n : nat) : (term592 x d p n) = (term46 x p n).
Proof. exact (@lem235526 (Nat.pow p d) x (Nat.pow p n)). Qed.
Lemma lem235528 (d : nat) (x : nat) (p : nat) (n : nat) : (term360 x d p n) = (term46 x p n).
Proof. exact (TRANS (@lem235524 x d p n) (@lem235527 d x p n)). Qed.
Lemma lem235529 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem235530 (d : nat) (x : nat) (p : nat) (n : nat) : (term593 x d p n) = (term594 x p n).
Proof. exact (MK_COMB (@lem235529) (@lem235528 d x p n)). Qed.
Lemma lem235531 (x : nat) (p : nat) (n : nat) : (term46 x p n) = (term46 x p n).
Proof. exact (eq_refl (term46 x p n)). Qed.
Lemma lem235532 (d : nat) (x : nat) (p : nat) (n : nat) : ((term360 x d p n) = (term46 x p n)) = ((term46 x p n) = (term46 x p n)).
Proof. exact (MK_COMB (@lem235530 d x p n) (@lem235531 x p n)). Qed.
Lemma lem235534 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem235535 (x : nat) : (x = x) = True.
Proof. exact (@lem235534 nat x). Qed.
Lemma lem235536 (x : nat) (p : nat) (n : nat) : ((term46 x p n) = (term46 x p n)) = True.
Proof. exact (@lem235535 (term46 x p n)). Qed.
Lemma lem235537 (d : nat) (x : nat) (p : nat) (n : nat) : ((term360 x d p n) = (term46 x p n)) = True.
Proof. exact (TRANS (@lem235532 d x p n) (@lem235536 x p n)). Qed.
Lemma lem235538 (d : nat) (x : nat) (p : nat) (n : nat) : True = ((term360 x d p n) = (term46 x p n)).
Proof. exact (SYM (@lem235537 d x p n)). Qed.
Lemma lem235539 (d : nat) (x : nat) (p : nat) (n : nat) : (term360 x d p n) = (term46 x p n).
Proof. exact (EQ_MP (@lem235538 d x p n) (@lem0)). Qed.
Lemma lem235540 (x : nat) (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term50 x m p n) = (term46 x p n).
Proof. exact (EQ_MP (@lem234154 x p m n d h1) (@lem235539 d x p n)). Qed.
Lemma lem235541 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term31 m n) : (term50 x m p n) = (term46 x p n).
Proof. exact (ex_elim (@lem234140 m n h1) (fun d : nat => fun h0 : term356 m n d => @lem235540 x p m n d h0)). Qed.
Lemma lem235542 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : (term31 m n) = ((term50 x m p n) = (term46 x p n)).
Proof. exact (prop_ext (fun h3 : term31 m n => @lem235541 x p m n h3) (fun h3 : (term50 x m p n) = (term46 x p n) => @lem235468 m n p h1 h2)). Qed.
Lemma lem235543 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : (term50 x m p n) = (term46 x p n).
Proof. exact (EQ_MP (@lem235542 x m n p h1 h2) (@lem235468 m n p h1 h2)). Qed.
Lemma lem235544 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term34 m n) (h2 : term41 p) : (term50 x m p n) = (term271 x p m n).
Proof. exact (EQ_MP (@lem233595 x p m n h1) (@lem235543 x m n p h1 h2)). Qed.
Lemma lem235545 (x : nat) (p : nat) (m : nat) (n : nat) (h1 : term41 p) (h2 : Peano.le m n) : (term50 x m p n) = (term271 x p m n).
Proof. exact (EQ_MP (@lem233556 x p m n h2) (@lem234139 x p m n h1 h2)). Qed.
Lemma lem235546 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 p) : (term50 x m p n) = (term271 x p m n).
Proof. exact (or_elim (@lem231416 m n) (fun h0 : Peano.le m n => @lem235545 x p m n h1 h0) (fun h0 : term34 m n => @lem235544 x m n p h0 h1)). Qed.
Lemma lem235547 (x : nat) (m : nat) (n : nat) (p : nat) (h1 : term41 p) : (term50 x m p n) = (term57 x p m n).
Proof. exact (EQ_MP (@lem233517 x p m n) (@lem235546 x m n p h1)). Qed.
Lemma lem235548 (x : nat) (p : nat) (m : nat) (n : nat) : (term50 x m p n) = (term57 x p m n).
Proof. exact (or_elim (@lem231447 p) (fun h0 : p = (NUMERAL 0) => @lem233504 x m n p h0) (fun h0 : term41 p => @lem235547 x m n p h0)). Qed.
Lemma lem235553 (x : nat) (p : nat) (m : nat) : term595 x p m.
Proof. exact (fun n : nat => @lem235548 x p m n). Qed.
Lemma lem235558 (x : nat) (p : nat) : term596 x p.
Proof. exact (fun m : nat => @lem235553 x p m). Qed.
Lemma lem235563 (x : nat) : term597 x.
Proof. exact (fun p : nat => @lem235558 x p). Qed.
Lemma lem235568 : term598.
Proof. exact (fun x : nat => @lem235563 x). Qed.
