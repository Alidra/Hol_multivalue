Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_SUB_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import EVEN_SUB_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EVEN_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem145382 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem145383 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem145382 n h1)). Qed.
Lemma lem145384 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem145385 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem145384 n h1)). Qed.
Lemma lem145386 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem145383 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem145385 n h1)). Qed.
Lemma lem145387 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem145386 n)). Qed.
Lemma lem145388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem145389 : term3 = term4.
Proof. exact (MK_COMB (@lem145388) (@lem145387)). Qed.
Lemma lem145390 : term4.
Proof. exact (EQ_MP (@lem145389) (@lem124715)). Qed.
Lemma lem145391 (m : nat) : term5 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem145392 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem145393 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem145392 m) (@lem145391 m)). Qed.
Lemma lem145394 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem145393 m n). Qed.
Lemma lem145395 (n : nat) (m : nat) : (term7 m n) = ((term8 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem145397 (t1 : Prop) : term9 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem145398 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem145399 (t1 : Prop) : term10 t1.
Proof. exact (EQ_MP (@lem145398 t1) (@lem145397 t1)). Qed.
Lemma lem145400 (t1 : Prop) (t2 : Prop) : term11 t1 t2.
Proof. exact (@lem145399 t1 t2). Qed.
Lemma lem145401 (t1 : Prop) (t2 : Prop) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (eq_refl (term11 t1 t2)). Qed.
Lemma lem145402 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (EQ_MP (@lem145401 t1 t2) (@lem145400 t1 t2)). Qed.
Lemma lem145405 (m : nat) : term13 m.
Proof. exact (@lem145380 m). Qed.
Lemma lem145406 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem145407 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem145406 m) (@lem145405 m)). Qed.
Lemma lem145408 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem145407 m n). Qed.
Lemma lem145409 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem145411 (n : nat) : term18 n.
Proof. exact (@lem145390 n). Qed.
Lemma lem145412 (n : nat) : (term18 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem145425 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem145412 n) (@lem145411 n)). Qed.
Lemma lem145426 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem145425 (Nat.sub m n)). Qed.
Lemma lem145428 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem145409 m n) (@lem145408 m n)). Qed.
Lemma lem145433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145434 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem145433) (@lem145428 m n)). Qed.
Lemma lem145436 (t1 : Prop) (t2 : Prop) : (term22 t1 t2) = (term23 t1 t2).
Proof. exact (proj2 (@lem145402 t1 t2)). Qed.
Lemma lem145437 (m : nat) (n : nat) : (term21 m n) = (term24 m n).
Proof. exact (@lem145436 (Peano.le m n) ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem145441 (n : nat) (m : nat) : (term8 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem145395 n m) (@lem145394 m n)). Qed.
Lemma lem145442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem145443 (n : nat) (m : nat) : (term25 m n) = (term26 n m).
Proof. exact (MK_COMB (@lem145442) (@lem145441 n m)). Qed.
Lemma lem145446 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem145447 (m : nat) (n : nat) : (term24 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem145443 n m) (@lem145446 m n)). Qed.
Lemma lem145450 (m : nat) (n : nat) : (term21 m n) = (term28 m n).
Proof. exact (TRANS (@lem145437 m n) (@lem145447 m n)). Qed.
Lemma lem145451 (m : nat) (n : nat) : (term20 m n) = (term28 m n).
Proof. exact (TRANS (@lem145434 m n) (@lem145450 m n)). Qed.
Lemma lem145452 (m : nat) (n : nat) : (term19 m n) = (term28 m n).
Proof. exact (TRANS (@lem145426 m n) (@lem145451 m n)). Qed.
Lemma lem145453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145454 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem145453) (@lem145452 m n)). Qed.
Lemma lem145460 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem145412 n) (@lem145411 n)). Qed.
Lemma lem145461 (m : nat) : (Coq.Arith.PeanoNat.Nat.Odd m) = (term0 m).
Proof. exact (@lem145460 m). Qed.
Lemma lem145462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145463 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem145462) (@lem145461 m)). Qed.
Lemma lem145465 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem145412 n) (@lem145411 n)). Qed.
Lemma lem145466 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd m) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((term0 m) = (term0 n)).
Proof. exact (MK_COMB (@lem145463 m) (@lem145465 n)). Qed.
Lemma lem145469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145470 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem145469) (@lem145466 m n)). Qed.
Lemma lem145471 (n : nat) (m : nat) : (term26 n m) = (term26 n m).
Proof. exact (eq_refl (term26 n m)). Qed.
Lemma lem145472 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem145471 n m) (@lem145470 m n)). Qed.
Lemma lem145475 (m : nat) (n : nat) : ((term19 m n) = (term35 m n)) = ((term28 m n) = (term36 m n)).
Proof. exact (MK_COMB (@lem145454 m n) (@lem145472 m n)). Qed.
Lemma lem145478 (m : nat) : (term37 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem145475 m n)). Qed.
Lemma lem145479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem145480 (m : nat) : (term39 m) = (term40 m).
Proof. exact (MK_COMB (@lem145479) (@lem145478 m)). Qed.
Lemma lem145485 : term41 = term42.
Proof. exact (fun_ext (fun m : nat => @lem145480 m)). Qed.
Lemma lem145486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem145487 : term43 = term44.
Proof. exact (MK_COMB (@lem145486) (@lem145485)). Qed.
Lemma lem145492 : term44 = term43.
Proof. exact (SYM (@lem145487)). Qed.
Lemma lem145505 (n : nat) (m : nat) : term45 n m.
Proof. exact (@lem9851 (Peano.lt n m)). Qed.
Lemma lem145506 (n : nat) (m : nat) : (term45 n m) = (term46 n m).
Proof. exact (eq_refl (term45 n m)). Qed.
Lemma lem145507 (n : nat) (m : nat) : term46 n m.
Proof. exact (EQ_MP (@lem145506 n m) (@lem145505 n m)). Qed.
Lemma lem145508 (n : nat) (m : nat) (h1 : (Peano.lt n m) = True) : (Peano.lt n m) = True.
Proof. exact (h1). Qed.
Lemma lem145509 (n : nat) (m : nat) (h1 : (Peano.lt n m) = False) : (Peano.lt n m) = False.
Proof. exact (h1). Qed.
Lemma lem145522 (m : nat) (n : nat) : (term47 m n) = (term47 m n).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem145523 (n : nat) (m : nat) (h1 : (Peano.lt n m) = True) : (term48 n m) = (term49 m n).
Proof. exact (MK_COMB (@lem145522 m n) (@lem145508 n m h1)). Qed.
Lemma lem145524 (m : nat) (n : nat) : (term49 m n) = ((term50 m n) = (term51 m n)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem145525 (n : nat) (m : nat) : (term52 n m) = (term52 n m).
Proof. exact (eq_refl (term52 n m)). Qed.
Lemma lem145526 (m : nat) (n : nat) : ((term48 n m) = (term49 m n)) = ((term48 n m) = ((term50 m n) = (term51 m n))).
Proof. exact (MK_COMB (@lem145525 n m) (@lem145524 m n)). Qed.
Lemma lem145527 (m : nat) (n : nat) : (term48 n m) = ((term28 m n) = (term36 m n)).
Proof. exact (eq_refl (term48 n m)). Qed.
Lemma lem145528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145529 (m : nat) (n : nat) : (term52 n m) = (term53 m n).
Proof. exact (MK_COMB (@lem145528) (@lem145527 m n)). Qed.
Lemma lem145530 (m : nat) (n : nat) : ((term50 m n) = (term51 m n)) = ((term50 m n) = (term51 m n)).
Proof. exact (eq_refl ((term50 m n) = (term51 m n))). Qed.
Lemma lem145531 (m : nat) (n : nat) : ((term48 n m) = ((term50 m n) = (term51 m n))) = (((term28 m n) = (term36 m n)) = ((term50 m n) = (term51 m n))).
Proof. exact (MK_COMB (@lem145529 m n) (@lem145530 m n)). Qed.
Lemma lem145532 (m : nat) (n : nat) : ((term48 n m) = (term49 m n)) = (((term28 m n) = (term36 m n)) = ((term50 m n) = (term51 m n))).
Proof. exact (TRANS (@lem145526 m n) (@lem145531 m n)). Qed.
Lemma lem145533 (n : nat) (m : nat) (h1 : (Peano.lt n m) = True) : ((term28 m n) = (term36 m n)) = ((term50 m n) = (term51 m n)).
Proof. exact (EQ_MP (@lem145532 m n) (@lem145523 n m h1)). Qed.
Lemma lem145534 (n : nat) (m : nat) (h1 : (Peano.lt n m) = True) : ((term50 m n) = (term51 m n)) = ((term28 m n) = (term36 m n)).
Proof. exact (SYM (@lem145533 n m h1)). Qed.
Lemma lem145535 (m : nat) (n : nat) : (term47 m n) = (term47 m n).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem145536 (n : nat) (m : nat) (h1 : (Peano.lt n m) = False) : (term48 n m) = (term54 m n).
Proof. exact (MK_COMB (@lem145535 m n) (@lem145509 n m h1)). Qed.
Lemma lem145537 (m : nat) (n : nat) : (term54 m n) = ((term55 m n) = (term56 m n)).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem145538 (n : nat) (m : nat) : (term52 n m) = (term52 n m).
Proof. exact (eq_refl (term52 n m)). Qed.
Lemma lem145539 (m : nat) (n : nat) : ((term48 n m) = (term54 m n)) = ((term48 n m) = ((term55 m n) = (term56 m n))).
Proof. exact (MK_COMB (@lem145538 n m) (@lem145537 m n)). Qed.
Lemma lem145540 (m : nat) (n : nat) : (term48 n m) = ((term28 m n) = (term36 m n)).
Proof. exact (eq_refl (term48 n m)). Qed.
Lemma lem145541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145542 (m : nat) (n : nat) : (term52 n m) = (term53 m n).
Proof. exact (MK_COMB (@lem145541) (@lem145540 m n)). Qed.
Lemma lem145543 (m : nat) (n : nat) : ((term55 m n) = (term56 m n)) = ((term55 m n) = (term56 m n)).
Proof. exact (eq_refl ((term55 m n) = (term56 m n))). Qed.
Lemma lem145544 (m : nat) (n : nat) : ((term48 n m) = ((term55 m n) = (term56 m n))) = (((term28 m n) = (term36 m n)) = ((term55 m n) = (term56 m n))).
Proof. exact (MK_COMB (@lem145542 m n) (@lem145543 m n)). Qed.
Lemma lem145545 (m : nat) (n : nat) : ((term48 n m) = (term54 m n)) = (((term28 m n) = (term36 m n)) = ((term55 m n) = (term56 m n))).
Proof. exact (TRANS (@lem145539 m n) (@lem145544 m n)). Qed.
Lemma lem145546 (n : nat) (m : nat) (h1 : (Peano.lt n m) = False) : ((term28 m n) = (term36 m n)) = ((term55 m n) = (term56 m n)).
Proof. exact (EQ_MP (@lem145545 m n) (@lem145536 n m h1)). Qed.
Lemma lem145547 (n : nat) (m : nat) (h1 : (Peano.lt n m) = False) : ((term55 m n) = (term56 m n)) = ((term28 m n) = (term36 m n)).
Proof. exact (SYM (@lem145546 n m h1)). Qed.
Lemma lem145551 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem145552 (m : nat) (n : nat) : (term50 m n) = (term27 m n).
Proof. exact (@lem145551 (term27 m n)). Qed.
Lemma lem145555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145556 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem145555) (@lem145552 m n)). Qed.
Lemma lem145558 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem145559 (m : nat) (n : nat) : (term51 m n) = (term34 m n).
Proof. exact (@lem145558 (term34 m n)). Qed.
Lemma lem145562 (m : nat) (n : nat) : ((term50 m n) = (term51 m n)) = ((term27 m n) = (term34 m n)).
Proof. exact (MK_COMB (@lem145556 m n) (@lem145559 m n)). Qed.
Lemma lem145565 (m : nat) (n : nat) : ((term27 m n) = (term34 m n)) = ((term50 m n) = (term51 m n)).
Proof. exact (SYM (@lem145562 m n)). Qed.
Lemma lem145566 (m : nat) : term59 m.
Proof. exact (@lem9851 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145567 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem145568 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem145567 m) (@lem145566 m)). Qed.
Lemma lem145569 (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = True) : (Coq.Arith.PeanoNat.Nat.Even m) = True.
Proof. exact (h1). Qed.
Lemma lem145570 (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = False) : (Coq.Arith.PeanoNat.Nat.Even m) = False.
Proof. exact (h1). Qed.
Lemma lem145579 (n : nat) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem145580 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = True) : (term62 n m) = (term63 n).
Proof. exact (MK_COMB (@lem145579 n) (@lem145569 m h1)). Qed.
Lemma lem145581 (n : nat) : (term63 n) = ((term64 n) = (term65 n)).
Proof. exact (eq_refl (term63 n)). Qed.
Lemma lem145582 (n : nat) (m : nat) : (term66 n m) = (term66 n m).
Proof. exact (eq_refl (term66 n m)). Qed.
Lemma lem145583 (m : nat) (n : nat) : ((term62 n m) = (term63 n)) = ((term62 n m) = ((term64 n) = (term65 n))).
Proof. exact (MK_COMB (@lem145582 n m) (@lem145581 n)). Qed.
Lemma lem145584 (m : nat) (n : nat) : (term62 n m) = ((term27 m n) = (term34 m n)).
Proof. exact (eq_refl (term62 n m)). Qed.
Lemma lem145585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145586 (m : nat) (n : nat) : (term66 n m) = (term67 m n).
Proof. exact (MK_COMB (@lem145585) (@lem145584 m n)). Qed.
Lemma lem145587 (n : nat) : ((term64 n) = (term65 n)) = ((term64 n) = (term65 n)).
Proof. exact (eq_refl ((term64 n) = (term65 n))). Qed.
Lemma lem145588 (m : nat) (n : nat) : ((term62 n m) = ((term64 n) = (term65 n))) = (((term27 m n) = (term34 m n)) = ((term64 n) = (term65 n))).
Proof. exact (MK_COMB (@lem145586 m n) (@lem145587 n)). Qed.
Lemma lem145589 (m : nat) (n : nat) : ((term62 n m) = (term63 n)) = (((term27 m n) = (term34 m n)) = ((term64 n) = (term65 n))).
Proof. exact (TRANS (@lem145583 m n) (@lem145588 m n)). Qed.
Lemma lem145590 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = True) : ((term27 m n) = (term34 m n)) = ((term64 n) = (term65 n)).
Proof. exact (EQ_MP (@lem145589 m n) (@lem145580 n m h1)). Qed.
Lemma lem145591 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = True) : ((term64 n) = (term65 n)) = ((term27 m n) = (term34 m n)).
Proof. exact (SYM (@lem145590 n m h1)). Qed.
Lemma lem145592 (n : nat) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem145593 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = False) : (term62 n m) = (term68 n).
Proof. exact (MK_COMB (@lem145592 n) (@lem145570 m h1)). Qed.
Lemma lem145594 (n : nat) : (term68 n) = ((term69 n) = (term70 n)).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem145595 (n : nat) (m : nat) : (term66 n m) = (term66 n m).
Proof. exact (eq_refl (term66 n m)). Qed.
Lemma lem145596 (m : nat) (n : nat) : ((term62 n m) = (term68 n)) = ((term62 n m) = ((term69 n) = (term70 n))).
Proof. exact (MK_COMB (@lem145595 n m) (@lem145594 n)). Qed.
Lemma lem145597 (m : nat) (n : nat) : (term62 n m) = ((term27 m n) = (term34 m n)).
Proof. exact (eq_refl (term62 n m)). Qed.
Lemma lem145598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145599 (m : nat) (n : nat) : (term66 n m) = (term67 m n).
Proof. exact (MK_COMB (@lem145598) (@lem145597 m n)). Qed.
Lemma lem145600 (n : nat) : ((term69 n) = (term70 n)) = ((term69 n) = (term70 n)).
Proof. exact (eq_refl ((term69 n) = (term70 n))). Qed.
Lemma lem145601 (m : nat) (n : nat) : ((term62 n m) = ((term69 n) = (term70 n))) = (((term27 m n) = (term34 m n)) = ((term69 n) = (term70 n))).
Proof. exact (MK_COMB (@lem145599 m n) (@lem145600 n)). Qed.
Lemma lem145602 (m : nat) (n : nat) : ((term62 n m) = (term68 n)) = (((term27 m n) = (term34 m n)) = ((term69 n) = (term70 n))).
Proof. exact (TRANS (@lem145596 m n) (@lem145601 m n)). Qed.
Lemma lem145603 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = False) : ((term27 m n) = (term34 m n)) = ((term69 n) = (term70 n)).
Proof. exact (EQ_MP (@lem145602 m n) (@lem145593 n m h1)). Qed.
Lemma lem145604 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = False) : ((term69 n) = (term70 n)) = ((term27 m n) = (term34 m n)).
Proof. exact (SYM (@lem145603 n m h1)). Qed.
Lemma lem145608 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem145609 (n : nat) : (True = (Coq.Arith.PeanoNat.Nat.Even n)) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145608 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145611 (n : nat) : (term64 n) = (term0 n).
Proof. exact (MK_COMB (@lem145610) (@lem145609 n)). Qed.
Lemma lem145612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145613 (n : nat) : (term71 n) = (term32 n).
Proof. exact (MK_COMB (@lem145612) (@lem145611 n)). Qed.
Lemma lem145617 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem145618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145619 : term72 = (@eq Prop False).
Proof. exact (MK_COMB (@lem145618) (@lem145617)). Qed.
Lemma lem145620 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem145621 (n : nat) : ((~ True) = (term0 n)) = (False = (term0 n)).
Proof. exact (MK_COMB (@lem145619) (@lem145620 n)). Qed.
Lemma lem145623 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem145624 (n : nat) : (False = (term0 n)) = (term73 n).
Proof. exact (@lem145623 (term0 n)). Qed.
Lemma lem145626 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem145627 (n : nat) : (term73 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145626 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145628 (n : nat) : (False = (term0 n)) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem145624 n) (@lem145627 n)). Qed.
Lemma lem145629 (n : nat) : ((~ True) = (term0 n)) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem145621 n) (@lem145628 n)). Qed.
Lemma lem145630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145631 (n : nat) : (term65 n) = (term0 n).
Proof. exact (MK_COMB (@lem145630) (@lem145629 n)). Qed.
Lemma lem145632 (n : nat) : ((term64 n) = (term65 n)) = ((term0 n) = (term0 n)).
Proof. exact (MK_COMB (@lem145613 n) (@lem145631 n)). Qed.
Lemma lem145634 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem145635 (x : Prop) : (x = x) = True.
Proof. exact (@lem145634 Prop x). Qed.
Lemma lem145636 (n : nat) : ((term0 n) = (term0 n)) = True.
Proof. exact (@lem145635 (term0 n)). Qed.
Lemma lem145637 (n : nat) : ((term64 n) = (term65 n)) = True.
Proof. exact (TRANS (@lem145632 n) (@lem145636 n)). Qed.
Lemma lem145638 (n : nat) : True = ((term64 n) = (term65 n)).
Proof. exact (SYM (@lem145637 n)). Qed.
Lemma lem145639 (n : nat) : (term64 n) = (term65 n).
Proof. exact (EQ_MP (@lem145638 n) (@lem0)). Qed.
Lemma lem145643 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem145644 (n : nat) : (False = (Coq.Arith.PeanoNat.Nat.Even n)) = (term0 n).
Proof. exact (@lem145643 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145645 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145646 (n : nat) : (term69 n) = (term73 n).
Proof. exact (MK_COMB (@lem145645) (@lem145644 n)). Qed.
Lemma lem145648 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem145649 (n : nat) : (term73 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145648 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145650 (n : nat) : (term69 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem145646 n) (@lem145649 n)). Qed.
Lemma lem145651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145652 (n : nat) : (term75 n) = (term76 n).
Proof. exact (MK_COMB (@lem145651) (@lem145650 n)). Qed.
Lemma lem145656 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem145657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145658 : term77 = (@eq Prop True).
Proof. exact (MK_COMB (@lem145657) (@lem145656)). Qed.
Lemma lem145659 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem145660 (n : nat) : ((~ False) = (term0 n)) = (True = (term0 n)).
Proof. exact (MK_COMB (@lem145658) (@lem145659 n)). Qed.
Lemma lem145662 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem145663 (n : nat) : (True = (term0 n)) = (term0 n).
Proof. exact (@lem145662 (term0 n)). Qed.
Lemma lem145664 (n : nat) : ((~ False) = (term0 n)) = (term0 n).
Proof. exact (TRANS (@lem145660 n) (@lem145663 n)). Qed.
Lemma lem145665 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem145666 (n : nat) : (term70 n) = (term73 n).
Proof. exact (MK_COMB (@lem145665) (@lem145664 n)). Qed.
Lemma lem145668 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem145669 (n : nat) : (term73 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145668 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145670 (n : nat) : (term70 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem145666 n) (@lem145669 n)). Qed.
Lemma lem145671 (n : nat) : ((term69 n) = (term70 n)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem145652 n) (@lem145670 n)). Qed.
Lemma lem145673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem145674 (x : Prop) : (x = x) = True.
Proof. exact (@lem145673 Prop x). Qed.
Lemma lem145675 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (@lem145674 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145676 (n : nat) : ((term69 n) = (term70 n)) = True.
Proof. exact (TRANS (@lem145671 n) (@lem145675 n)). Qed.
Lemma lem145677 (n : nat) : True = ((term69 n) = (term70 n)).
Proof. exact (SYM (@lem145676 n)). Qed.
Lemma lem145678 (n : nat) : (term69 n) = (term70 n).
Proof. exact (EQ_MP (@lem145677 n) (@lem0)). Qed.
Lemma lem145679 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = False) : (term27 m n) = (term34 m n).
Proof. exact (EQ_MP (@lem145604 n m h1) (@lem145678 n)). Qed.
Lemma lem145680 (n : nat) (m : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = True) : (term27 m n) = (term34 m n).
Proof. exact (EQ_MP (@lem145591 n m h1) (@lem145639 n)). Qed.
Lemma lem145682 (m : nat) (n : nat) : (term27 m n) = (term34 m n).
Proof. exact (or_elim (@lem145568 m) (fun h0 : (Coq.Arith.PeanoNat.Nat.Even m) = True => @lem145680 n m h0) (fun h0 : (Coq.Arith.PeanoNat.Nat.Even m) = False => @lem145679 n m h0)). Qed.
Lemma lem145683 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (EQ_MP (@lem145565 m n) (@lem145682 m n)). Qed.
Lemma lem145687 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem145688 (m : nat) (n : nat) : (term55 m n) = False.
Proof. exact (@lem145687 (term27 m n)). Qed.
Lemma lem145689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145690 (m : nat) (n : nat) : (term78 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem145689) (@lem145688 m n)). Qed.
Lemma lem145692 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem145693 (m : nat) (n : nat) : (term56 m n) = False.
Proof. exact (@lem145692 (term34 m n)). Qed.
Lemma lem145694 (m : nat) (n : nat) : ((term55 m n) = (term56 m n)) = (False = False).
Proof. exact (MK_COMB (@lem145690 m n) (@lem145693 m n)). Qed.
Lemma lem145696 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem145697 : (False = False) = (~ False).
Proof. exact (@lem145696 False). Qed.
Lemma lem145699 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem145700 : (False = False) = True.
Proof. exact (TRANS (@lem145697) (@lem145699)). Qed.
Lemma lem145701 (m : nat) (n : nat) : ((term55 m n) = (term56 m n)) = True.
Proof. exact (TRANS (@lem145694 m n) (@lem145700)). Qed.
Lemma lem145702 (m : nat) (n : nat) : True = ((term55 m n) = (term56 m n)).
Proof. exact (SYM (@lem145701 m n)). Qed.
Lemma lem145703 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem145702 m n) (@lem0)). Qed.
Lemma lem145704 (n : nat) (m : nat) (h1 : (Peano.lt n m) = False) : (term28 m n) = (term36 m n).
Proof. exact (EQ_MP (@lem145547 n m h1) (@lem145703 m n)). Qed.
Lemma lem145705 (n : nat) (m : nat) (h1 : (Peano.lt n m) = True) : (term28 m n) = (term36 m n).
Proof. exact (EQ_MP (@lem145534 n m h1) (@lem145683 m n)). Qed.
Lemma lem145708 (m : nat) (n : nat) : (term28 m n) = (term36 m n).
Proof. exact (or_elim (@lem145507 n m) (fun h0 : (Peano.lt n m) = True => @lem145705 n m h0) (fun h0 : (Peano.lt n m) = False => @lem145704 n m h0)). Qed.
Lemma lem145713 (m : nat) : term40 m.
Proof. exact (fun n : nat => @lem145708 m n). Qed.
Lemma lem145718 : term44.
Proof. exact (fun m : nat => @lem145713 m). Qed.
Lemma lem145719 : term43.
Proof. exact (EQ_MP (@lem145492) (@lem145718)). Qed.
