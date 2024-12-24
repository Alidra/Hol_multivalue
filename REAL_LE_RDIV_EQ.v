Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RDIV_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import REAL_LT_IMP_NZ_spec.
Require Import REAL_MUL_RID_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1340174_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1628378 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1628379 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1628378 x y z h1)). Qed.
Lemma lem1628380 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1628381 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1628380 x y z h1)). Qed.
Lemma lem1628382 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1628379 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1628381 x y z h1)). Qed.
Lemma lem1628383 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1628382 x y z)). Qed.
Lemma lem1628384 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628385 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1628384) (@lem1628383 x y)). Qed.
Lemma lem1628386 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1628385 x y)). Qed.
Lemma lem1628387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628388 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1628387) (@lem1628386 x)). Qed.
Lemma lem1628389 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1628388 x)). Qed.
Lemma lem1628390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628391 : term12 = term13.
Proof. exact (MK_COMB (@lem1628390) (@lem1628389)). Qed.
Lemma lem1628392 : term13.
Proof. exact (EQ_MP (@lem1628391) (@lem1338912)). Qed.
Lemma lem1628393 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (h1). Qed.
Lemma lem1628394 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1628395 (x : real) (h1 : term15) : term16 x.
Proof. exact (@lem1628394 h1 x). Qed.
Lemma lem1628396 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1628397 (x : real) (h1 : term15) : term17 x.
Proof. exact (EQ_MP (@lem1628396 x) (@lem1628395 x h1)). Qed.
Lemma lem1628398 (x : real) (y : real) (h1 : term15) : term18 x y.
Proof. exact (@lem1628397 x h1 y). Qed.
Lemma lem1628399 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1628400 (x : real) (y : real) (h1 : term15) : term19 x y.
Proof. exact (EQ_MP (@lem1628399 x y) (@lem1628398 x y h1)). Qed.
Lemma lem1628401 (x : real) (y : real) (z : real) (h1 : term15) : term20 x y z.
Proof. exact (@lem1628400 x y h1 z). Qed.
Lemma lem1628402 (z : real) (x : real) (y : real) : (term20 x y z) = (term21 z x y).
Proof. exact (eq_refl (term20 x y z)). Qed.
Lemma lem1628403 (z : real) (x : real) (y : real) (h1 : term15) : term21 z x y.
Proof. exact (EQ_MP (@lem1628402 z x y) (@lem1628401 x y z h1)). Qed.
Lemma lem1628404 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (h1). Qed.
Lemma lem1628405 (x : real) (y : real) (z : real) (h1 : term15) (h2 : term14 z) : (term22 x y z) = (real_le x y).
Proof. exact (@lem1628403 z x y h1 (@lem1628404 z h2)). Qed.
Lemma lem1628406 (x : real) (z : real) (h1 : term15) (h2 : term14 z) : term23 z x.
Proof. exact (fun y : real => @lem1628405 x y z h1 h2). Qed.
Lemma lem1628407 (z : real) (h1 : term15) (h2 : term14 z) : term24 z.
Proof. exact (fun x : real => @lem1628406 x z h1 h2). Qed.
Lemma lem1628408 (z : real) (h1 : term15) : term25 z.
Proof. exact (fun h0 : term14 z => @lem1628407 z h1 h0). Qed.
Lemma lem1628409 (h1 : term15) : term26.
Proof. exact (fun z : real => @lem1628408 z h1). Qed.
Lemma lem1628410 : term27.
Proof. exact (fun h0 : term15 => @lem1628409 h0). Qed.
Lemma lem1628411 : term26.
Proof. exact (@lem1628410 (@lem1600741)). Qed.
Lemma lem1628412 (z : real) : term28 z.
Proof. exact (@lem1628411 z). Qed.
Lemma lem1628413 (z : real) : (term28 z) = (term25 z).
Proof. exact (eq_refl (term28 z)). Qed.
Lemma lem1628416 (z : real) : term25 z.
Proof. exact (EQ_MP (@lem1628413 z) (@lem1628412 z)). Qed.
Lemma lem1628417 (z : real) (h1 : term14 z) : term24 z.
Proof. exact (@lem1628416 z (@lem1628393 z h1)). Qed.
Lemma lem1628420 (z : real) (x : real) (y : real) (h1 : (term22 x y z) = (real_le x y)) : (term22 x y z) = (real_le x y).
Proof. exact (h1). Qed.
Lemma lem1628421 (z : real) (x : real) (y : real) (h1 : (term22 x y z) = (real_le x y)) : (real_le x y) = (term22 x y z).
Proof. exact (SYM (@lem1628420 z x y h1)). Qed.
Lemma lem1628422 (x : real) (y : real) (z : real) (h1 : (real_le x y) = (term22 x y z)) : (real_le x y) = (term22 x y z).
Proof. exact (h1). Qed.
Lemma lem1628423 (x : real) (y : real) (z : real) (h1 : (real_le x y) = (term22 x y z)) : (term22 x y z) = (real_le x y).
Proof. exact (SYM (@lem1628422 x y z h1)). Qed.
Lemma lem1628424 (x : real) (y : real) (z : real) : ((term22 x y z) = (real_le x y)) = ((real_le x y) = (term22 x y z)).
Proof. exact (prop_ext (fun h1 : (term22 x y z) = (real_le x y) => @lem1628421 z x y h1) (fun h1 : (real_le x y) = (term22 x y z) => @lem1628423 x y z h1)). Qed.
Lemma lem1628425 (x : real) (z : real) : (term29 z x) = (term30 x z).
Proof. exact (fun_ext (fun y : real => @lem1628424 x y z)). Qed.
Lemma lem1628426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628427 (x : real) (z : real) : (term23 z x) = (term31 x z).
Proof. exact (MK_COMB (@lem1628426) (@lem1628425 x z)). Qed.
Lemma lem1628428 (z : real) : (term32 z) = (term33 z).
Proof. exact (fun_ext (fun x : real => @lem1628427 x z)). Qed.
Lemma lem1628429 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628430 (z : real) : (term24 z) = (term34 z).
Proof. exact (MK_COMB (@lem1628429) (@lem1628428 z)). Qed.
Lemma lem1628431 (z : real) (h1 : term14 z) : term34 z.
Proof. exact (EQ_MP (@lem1628430 z) (@lem1628417 z h1)). Qed.
Lemma lem1628432 (x : real) (z : real) (h1 : term14 z) : term35 z x.
Proof. exact (@lem1628431 z h1 x). Qed.
Lemma lem1628433 (x : real) (z : real) : (term35 z x) = (term31 x z).
Proof. exact (eq_refl (term35 z x)). Qed.
Lemma lem1628434 (x : real) (z : real) (h1 : term14 z) : term31 x z.
Proof. exact (EQ_MP (@lem1628433 x z) (@lem1628432 x z h1)). Qed.
Lemma lem1628435 (x : real) (y : real) (z : real) (h1 : term14 z) : term36 x z y.
Proof. exact (@lem1628434 x z h1 y). Qed.
Lemma lem1628436 (x : real) (y : real) (z : real) : (term36 x z y) = ((real_le x y) = (term22 x y z)).
Proof. exact (eq_refl (term36 x z y)). Qed.
Lemma lem1628439 (x : real) (y : real) (z : real) (h1 : term14 z) : (real_le x y) = (term22 x y z).
Proof. exact (EQ_MP (@lem1628436 x y z) (@lem1628435 x y z h1)). Qed.
Lemma lem1628440 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x y z) = (term38 x y z).
Proof. exact (@lem1628439 x (real_div y z) z h1). Qed.
Lemma lem1628441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1628442 (x : real) (y : real) (z : real) (h1 : term14 z) : (term39 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1628441) (@lem1628440 x y z h1)). Qed.
Lemma lem1628443 (x : real) (z : real) (y : real) : (term41 x z y) = (term41 x z y).
Proof. exact (eq_refl (term41 x z y)). Qed.
Lemma lem1628444 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term37 x y z) = (term41 x z y)) = ((term38 x y z) = (term41 x z y)).
Proof. exact (MK_COMB (@lem1628442 x y z h1) (@lem1628443 x z y)). Qed.
Lemma lem1628445 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x z y)) = ((term37 x y z) = (term41 x z y)).
Proof. exact (SYM (@lem1628444 x y z h1)). Qed.
Lemma lem1628446 (x : real) : term42 x.
Proof. exact (@lem1523977 x). Qed.
Lemma lem1628447 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1628448 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1628447 x) (@lem1628446 x)). Qed.
Lemma lem1628449 (x : real) (h1 : term14 x) : term14 x.
Proof. exact (h1). Qed.
Lemma lem1628450 (x : real) (h1 : term14 x) : term44 x.
Proof. exact (@lem1628448 x (@lem1628449 x h1)). Qed.
Lemma lem1628451 (x : real) : term45 x.
Proof. exact (@lem82 (x = term46)). Qed.
Lemma lem1628452 (x : real) (h1 : term14 x) : (x = term46) = False.
Proof. exact (@lem1628451 x (@lem1628450 x h1)). Qed.
Lemma lem1628474 (x : real) : term47 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1628475 (x : real) : (term47 x) = ((term48 x) = x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1628477 (x : real) : term49 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1628478 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1628479 (x : real) : term50 x.
Proof. exact (EQ_MP (@lem1628478 x) (@lem1628477 x)). Qed.
Lemma lem1628480 (x : real) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1628481 (x : real) (h1 : term44 x) : (term51 x) = term52.
Proof. exact (@lem1628479 x (@lem1628480 x h1)). Qed.
Lemma lem1628487 (x : real) : term53 x.
Proof. exact (@lem1628392 x). Qed.
Lemma lem1628488 (x : real) : (term53 x) = (term9 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1628489 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1628488 x) (@lem1628487 x)). Qed.
Lemma lem1628490 (x : real) (y : real) : term54 x y.
Proof. exact (@lem1628489 x y). Qed.
Lemma lem1628491 (x : real) (y : real) : (term54 x y) = (term5 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1628492 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1628491 x y) (@lem1628490 x y)). Qed.
Lemma lem1628493 (x : real) (y : real) (z : real) : term55 x y z.
Proof. exact (@lem1628492 x y z). Qed.
Lemma lem1628494 (x : real) (y : real) (z : real) : (term55 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term55 x y z)). Qed.
Lemma lem1628496 (x : real) : term56 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1628497 (x : real) : (term56 x) = (term57 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1628498 (x : real) : term57 x.
Proof. exact (EQ_MP (@lem1628497 x) (@lem1628496 x)). Qed.
Lemma lem1628499 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1628498 x y). Qed.
Lemma lem1628500 (x : real) (y : real) : (term58 x y) = ((real_div x y) = (term59 x y)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1628502 (z : real) : (term14 z) = ((term14 z) = True).
Proof. exact (@lem7 (term14 z)). Qed.
Lemma lem1628507 (x : real) (y : real) : (real_div x y) = (term59 x y).
Proof. exact (EQ_MP (@lem1628500 x y) (@lem1628499 x y)). Qed.
Lemma lem1628508 (y : real) (z : real) : (real_div y z) = (term59 y z).
Proof. exact (@lem1628507 y z). Qed.
Lemma lem1628509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1628510 (y : real) (z : real) : (term60 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1628509) (@lem1628508 y z)). Qed.
Lemma lem1628511 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1628512 (y : real) (z : real) : (term62 y z) = (term63 y z).
Proof. exact (MK_COMB (@lem1628510 y z) (@lem1628511 z)). Qed.
Lemma lem1628514 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1628494 x y z) (@lem1628493 x y z)). Qed.
Lemma lem1628515 (y : real) (z : real) : (term63 y z) = (term64 y z).
Proof. exact (@lem1628514 y (real_inv z) z). Qed.
Lemma lem1628517 (x : real) : term50 x.
Proof. exact (fun h0 : term44 x => @lem1628481 x h0). Qed.
Lemma lem1628518 (z : real) : term50 z.
Proof. exact (@lem1628517 z). Qed.
Lemma lem1628520 (x : real) : term65 x.
Proof. exact (fun h0 : term14 x => @lem1628452 x h0). Qed.
Lemma lem1628521 (z : real) : term65 z.
Proof. exact (@lem1628520 z). Qed.
Lemma lem1628523 (z : real) (h1 : term14 z) : (term14 z) = True.
Proof. exact (EQ_MP (@lem1628502 z) (@lem1628393 z h1)). Qed.
Lemma lem1628524 (z : real) (h1 : term14 z) : True = (term14 z).
Proof. exact (SYM (@lem1628523 z h1)). Qed.
Lemma lem1628525 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (EQ_MP (@lem1628524 z h1) (@lem0)). Qed.
Lemma lem1628526 (z : real) (h1 : term14 z) : (z = term46) = False.
Proof. exact (@lem1628521 z (@lem1628525 z h1)). Qed.
Lemma lem1628527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1628528 (z : real) (h1 : term14 z) : (term44 z) = (~ False).
Proof. exact (MK_COMB (@lem1628527) (@lem1628526 z h1)). Qed.
Lemma lem1628530 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1628531 (z : real) (h1 : term14 z) : (term44 z) = True.
Proof. exact (TRANS (@lem1628528 z h1) (@lem1628530)). Qed.
Lemma lem1628532 (z : real) (h1 : term14 z) : True = (term44 z).
Proof. exact (SYM (@lem1628531 z h1)). Qed.
Lemma lem1628533 (z : real) (h1 : term14 z) : term44 z.
Proof. exact (EQ_MP (@lem1628532 z h1) (@lem0)). Qed.
Lemma lem1628534 (z : real) (h1 : term14 z) : (term51 z) = term52.
Proof. exact (@lem1628518 z (@lem1628533 z h1)). Qed.
Lemma lem1628535 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1628536 (y : real) (z : real) (h1 : term14 z) : (term64 y z) = (term48 y).
Proof. exact (MK_COMB (@lem1628535 y) (@lem1628534 z h1)). Qed.
Lemma lem1628538 (x : real) : (term48 x) = x.
Proof. exact (EQ_MP (@lem1628475 x) (@lem1628474 x)). Qed.
Lemma lem1628539 (y : real) : (term48 y) = y.
Proof. exact (@lem1628538 y). Qed.
Lemma lem1628540 (y : real) (z : real) (h1 : term14 z) : (term64 y z) = y.
Proof. exact (TRANS (@lem1628536 y z h1) (@lem1628539 y)). Qed.
Lemma lem1628541 (y : real) (z : real) (h1 : term14 z) : (term63 y z) = y.
Proof. exact (TRANS (@lem1628515 y z) (@lem1628540 y z h1)). Qed.
Lemma lem1628542 (y : real) (z : real) (h1 : term14 z) : (term62 y z) = y.
Proof. exact (TRANS (@lem1628512 y z) (@lem1628541 y z h1)). Qed.
Lemma lem1628543 (x : real) (z : real) : (term66 x z) = (term66 x z).
Proof. exact (eq_refl (term66 x z)). Qed.
Lemma lem1628544 (x : real) (y : real) (z : real) (h1 : term14 z) : (term38 x y z) = (term41 x z y).
Proof. exact (MK_COMB (@lem1628543 x z) (@lem1628542 y z h1)). Qed.
Lemma lem1628545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1628546 (x : real) (y : real) (z : real) (h1 : term14 z) : (term40 x y z) = (term67 x z y).
Proof. exact (MK_COMB (@lem1628545) (@lem1628544 x y z h1)). Qed.
Lemma lem1628547 (x : real) (z : real) (y : real) : (term41 x z y) = (term41 x z y).
Proof. exact (eq_refl (term41 x z y)). Qed.
Lemma lem1628548 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x z y)) = ((term41 x z y) = (term41 x z y)).
Proof. exact (MK_COMB (@lem1628546 x y z h1) (@lem1628547 x z y)). Qed.
Lemma lem1628550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1628551 (x : Prop) : (x = x) = True.
Proof. exact (@lem1628550 Prop x). Qed.
Lemma lem1628552 (x : real) (z : real) (y : real) : ((term41 x z y) = (term41 x z y)) = True.
Proof. exact (@lem1628551 (term41 x z y)). Qed.
Lemma lem1628553 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x z y)) = True.
Proof. exact (TRANS (@lem1628548 x y z h1) (@lem1628552 x z y)). Qed.
Lemma lem1628554 (x : real) (y : real) (z : real) (h1 : term14 z) : True = ((term38 x y z) = (term41 x z y)).
Proof. exact (SYM (@lem1628553 x y z h1)). Qed.
Lemma lem1628555 (x : real) (y : real) (z : real) (h1 : term14 z) : (term38 x y z) = (term41 x z y).
Proof. exact (EQ_MP (@lem1628554 x y z h1) (@lem0)). Qed.
Lemma lem1628556 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x y z) = (term41 x z y).
Proof. exact (EQ_MP (@lem1628445 x y z h1) (@lem1628555 x y z h1)). Qed.
Lemma lem1628557 (x : real) (y : real) (z : real) (h1 : term14 z) : (term14 z) = ((term37 x y z) = (term41 x z y)).
Proof. exact (prop_ext (fun h2 : term14 z => @lem1628556 x y z h1) (fun h2 : (term37 x y z) = (term41 x z y) => @lem1628393 z h1)). Qed.
Lemma lem1628558 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x y z) = (term41 x z y).
Proof. exact (EQ_MP (@lem1628557 x y z h1) (@lem1628393 z h1)). Qed.
Lemma lem1628559 (x : real) (z : real) (y : real) : term68 x z y.
Proof. exact (fun h0 : term14 z => @lem1628558 x y z h0). Qed.
Lemma lem1628564 (x : real) (y : real) : term69 x y.
Proof. exact (fun z : real => @lem1628559 x z y). Qed.
Lemma lem1628569 (x : real) : term70 x.
Proof. exact (fun y : real => @lem1628564 x y). Qed.
Lemma lem1628574 : term71.
Proof. exact (fun x : real => @lem1628569 x). Qed.
