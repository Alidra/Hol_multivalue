Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import list_CASES_term_abbrevs.
Require Import CONS_11_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm82_spec.
Lemma lem1113447 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1113448 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1113449 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1113448 A h) (@lem1113447 A h)). Qed.
Lemma lem1113450 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1113449 A h t). Qed.
Lemma lem1113451 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1113452 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1113451 A h t) (@lem1113450 A h t)). Qed.
Lemma lem1113453 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1113456 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1113457 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1113456 A h t h1)). Qed.
Lemma lem1113458 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1113459 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1113458 A h t h1)). Qed.
Lemma lem1113460 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1113457 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1113459 A h t h1)). Qed.
Lemma lem1113461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1113462 {A : Type'} (h : A) (t : list A) : (term3 A h t) = (term5 A h t).
Proof. exact (MK_COMB (@lem1113461) (@lem1113460 A h t)). Qed.
Lemma lem1113463 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (EQ_MP (@lem1113462 A h t) (@lem1113452 A h t)). Qed.
Lemma lem1113464 {A : Type'} (h : A) (t : list A) : term6 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1113466 {A : Type'} (h1' : A) : term7 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1113467 {A : Type'} (h1' : A) : (term7 A h1') = (term8 A h1').
Proof. exact (eq_refl (term7 A h1')). Qed.
Lemma lem1113468 {A : Type'} (h1' : A) : term8 A h1'.
Proof. exact (EQ_MP (@lem1113467 A h1') (@lem1113466 A h1')). Qed.
Lemma lem1113469 {A : Type'} (h1' : A) (h2' : A) : term9 A h1' h2'.
Proof. exact (@lem1113468 A h1' h2'). Qed.
Lemma lem1113470 {A : Type'} (h1' : A) (h2' : A) : (term9 A h1' h2') = (term10 A h1' h2').
Proof. exact (eq_refl (term9 A h1' h2')). Qed.
Lemma lem1113471 {A : Type'} (h1' : A) (h2' : A) : term10 A h1' h2'.
Proof. exact (EQ_MP (@lem1113470 A h1' h2') (@lem1113469 A h1' h2')). Qed.
Lemma lem1113472 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term11 A h1' h2' t1.
Proof. exact (@lem1113471 A h1' h2' t1). Qed.
Lemma lem1113473 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term11 A h1' h2' t1) = (term12 A h1' h2' t1).
Proof. exact (eq_refl (term11 A h1' h2' t1)). Qed.
Lemma lem1113474 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term12 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1113473 A h1' h2' t1) (@lem1113472 A h1' h2' t1)). Qed.
Lemma lem1113475 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term13 A h1' h2' t1 t2.
Proof. exact (@lem1113474 A h1' h2' t1 t2). Qed.
Lemma lem1113476 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term13 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term14 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term13 A h1' h2' t1 t2)). Qed.
Lemma lem1113479 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1113480 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (@lem1113479 A P). Qed.
Lemma lem1113481 {A : Type'} : term16 A.
Proof. exact (@lem1113480 A (term17 A)). Qed.
Lemma lem1113482 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem1113483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113484 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem1113483) (@lem1113482 A)). Qed.
Lemma lem1113485 {A : Type'} (t : list A) : (term22 A t) = (term23 A t).
Proof. exact (eq_refl (term22 A t)). Qed.
Lemma lem1113486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1113487 {A : Type'} (t : list A) : (term24 A t) = (term25 A t).
Proof. exact (MK_COMB (@lem1113486) (@lem1113485 A t)). Qed.
Lemma lem1113488 {A : Type'} (h : A) (t : list A) : (term26 A h t) = (term27 A h t).
Proof. exact (eq_refl (term26 A h t)). Qed.
Lemma lem1113489 {A : Type'} (h : A) (t : list A) : (term28 A h t) = (term29 A h t).
Proof. exact (MK_COMB (@lem1113487 A t) (@lem1113488 A h t)). Qed.
Lemma lem1113490 {A : Type'} (h : A) : (term30 A h) = (term31 A h).
Proof. exact (fun_ext (fun t : list A => @lem1113489 A h t)). Qed.
Lemma lem1113491 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113492 {A : Type'} (h : A) : (term32 A h) = (term33 A h).
Proof. exact (MK_COMB (@lem1113491 A) (@lem1113490 A h)). Qed.
Lemma lem1113493 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun h : A => @lem1113492 A h)). Qed.
Lemma lem1113494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113495 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem1113494 A) (@lem1113493 A)). Qed.
Lemma lem1113496 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem1113484 A) (@lem1113495 A)). Qed.
Lemma lem1113497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1113498 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (MK_COMB (@lem1113497) (@lem1113496 A)). Qed.
Lemma lem1113499 {A : Type'} (l : list A) : (term22 A l) = (term23 A l).
Proof. exact (eq_refl (term22 A l)). Qed.
Lemma lem1113500 {A : Type'} : (term42 A) = (term17 A).
Proof. exact (fun_ext (fun l : list A => @lem1113499 A l)). Qed.
Lemma lem1113501 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113502 {A : Type'} : (term43 A) = (term44 A).
Proof. exact (MK_COMB (@lem1113501 A) (@lem1113500 A)). Qed.
Lemma lem1113503 {A : Type'} : (term16 A) = (term45 A).
Proof. exact (MK_COMB (@lem1113498 A) (@lem1113502 A)). Qed.
Lemma lem1113504 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem1113503 A) (@lem1113481 A)). Qed.
Lemma lem1113509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1113510 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1113509 (list A) x). Qed.
Lemma lem1113511 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1113510 A (@nil A)). Qed.
Lemma lem1113512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1113513 {A : Type'} : (term46 A) = (or True).
Proof. exact (MK_COMB (@lem1113512) (@lem1113511 A)). Qed.
Lemma lem1113523 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1113464 A h t (@lem1113463 A h t)). Qed.
Lemma lem1113524 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1113523 A h t). Qed.
Lemma lem1113525 {A : Type'} (h : A) : (term47 A h) = (term48 A).
Proof. exact (fun_ext (fun t : list A => @lem1113524 A h t)). Qed.
Lemma lem1113526 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113527 {A : Type'} (h : A) : (term49 A h) = (term50 A).
Proof. exact (MK_COMB (@lem1113526 A) (@lem1113525 A h)). Qed.
Lemma lem1113529 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1113530 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem1113529 (list A) t). Qed.
Lemma lem1113531 {A : Type'} : (term50 A) = False.
Proof. exact (@lem1113530 A False). Qed.
Lemma lem1113532 {A : Type'} (h : A) : (term49 A h) = False.
Proof. exact (TRANS (@lem1113527 A h) (@lem1113531 A)). Qed.
Lemma lem1113533 {A : Type'} : (term53 A) = (term54 A).
Proof. exact (fun_ext (fun h : A => @lem1113532 A h)). Qed.
Lemma lem1113534 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113535 {A : Type'} : (term55 A) = (term56 A).
Proof. exact (MK_COMB (@lem1113534 A) (@lem1113533 A)). Qed.
Lemma lem1113537 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1113538 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (@lem1113537 A t). Qed.
Lemma lem1113539 {A : Type'} : (term56 A) = False.
Proof. exact (@lem1113538 A False). Qed.
Lemma lem1113540 {A : Type'} : (term55 A) = False.
Proof. exact (TRANS (@lem1113535 A) (@lem1113539 A)). Qed.
Lemma lem1113541 {A : Type'} : (term19 A) = (True \/ False).
Proof. exact (MK_COMB (@lem1113513 A) (@lem1113540 A)). Qed.
Lemma lem1113543 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1113544 : (True \/ False) = True.
Proof. exact (@lem1113543 False). Qed.
Lemma lem1113545 {A : Type'} : (term19 A) = True.
Proof. exact (TRANS (@lem1113541 A) (@lem1113544)). Qed.
Lemma lem1113546 {A : Type'} : True = (term19 A).
Proof. exact (SYM (@lem1113545 A)). Qed.
Lemma lem1113547 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem1113546 A) (@lem0)). Qed.
Lemma lem1113551 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1113453 A h t (@lem1113452 A h t)). Qed.
Lemma lem1113552 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1113551 A h t). Qed.
Lemma lem1113553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1113554 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (or False).
Proof. exact (MK_COMB (@lem1113553) (@lem1113552 A h t)). Qed.
Lemma lem1113564 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term14 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1113476 A h1' h2' t1 t2) (@lem1113475 A h1' h2' t1 t2)). Qed.
Lemma lem1113565 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term14 A h1' h2' t1 t2).
Proof. exact (@lem1113564 A h1' h2' t1 t2). Qed.
Lemma lem1113566 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((@cons A h t) = (@cons A h' t')) = (term14 A h h' t t').
Proof. exact (@lem1113565 A h h' t t'). Qed.
Lemma lem1113573 {A : Type'} (h : A) (h' : A) (t : list A) : (term58 A h t h') = (term59 A h h' t).
Proof. exact (fun_ext (fun t' : list A => @lem1113566 A h h' t t')). Qed.
Lemma lem1113574 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113575 {A : Type'} (h : A) (h' : A) (t : list A) : (term60 A h t h') = (term61 A h h' t).
Proof. exact (MK_COMB (@lem1113574 A) (@lem1113573 A h h' t)). Qed.
Lemma lem1113580 {A : Type'} (h : A) (t : list A) : (term62 A h t) = (term63 A h t).
Proof. exact (fun_ext (fun h' : A => @lem1113575 A h h' t)). Qed.
Lemma lem1113581 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113582 {A : Type'} (h : A) (t : list A) : (term64 A h t) = (term65 A h t).
Proof. exact (MK_COMB (@lem1113581 A) (@lem1113580 A h t)). Qed.
Lemma lem1113587 {A : Type'} (h : A) (t : list A) : (term27 A h t) = (term66 A h t).
Proof. exact (MK_COMB (@lem1113554 A h t) (@lem1113582 A h t)). Qed.
Lemma lem1113589 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1113590 {A : Type'} (h : A) (t : list A) : (term66 A h t) = (term65 A h t).
Proof. exact (@lem1113589 (term65 A h t)). Qed.
Lemma lem1113605 {A : Type'} (h : A) (t : list A) : (term27 A h t) = (term65 A h t).
Proof. exact (TRANS (@lem1113587 A h t) (@lem1113590 A h t)). Qed.
Lemma lem1113606 {A : Type'} (h : A) (t : list A) : (term65 A h t) = (term27 A h t).
Proof. exact (SYM (@lem1113605 A h t)). Qed.
Lemma lem1113608 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1113609 {A : Type'} (h : A) (t : list A) : (term65 A h t) = (term68 A h t).
Proof. exact (@lem1113608 (term65 A h t)). Qed.
Lemma lem1113610 {A : Type'} (h : A) (t : list A) : (term68 A h t) = (term65 A h t).
Proof. exact (SYM (@lem1113609 A h t)). Qed.
Lemma lem1113611 {A : Type'} (h : A) (t : list A) (h1 : term69 A h t) : term69 A h t.
Proof. exact (h1). Qed.
Lemma lem1113614 {A : Type'} (h : A) (t : list A) (h1 : term68 A h t) : term68 A h t.
Proof. exact (h1). Qed.
Lemma lem1113615 {A : Type'} (h : A) (t : list A) : term70 A h t.
Proof. exact (fun h0 : term68 A h t => @lem1113614 A h t h0). Qed.
Lemma lem1113616 {A : Type'} (h : A) (t : list A) (h1 : term70 A h t) : term70 A h t.
Proof. exact (h1). Qed.
Lemma lem1113617 {A : Type'} (h : A) (t : list A) (h1 : term68 A h t) : term68 A h t.
Proof. exact (h1). Qed.
Lemma lem1113618 {A : Type'} (h : A) (t : list A) (h1 : term68 A h t) (h2 : term70 A h t) : term68 A h t.
Proof. exact (@lem1113616 A h t h2 (@lem1113617 A h t h1)). Qed.
Lemma lem1113619 {A : Type'} (h : A) (t : list A) (h1 : term68 A h t) : term71 A h t.
Proof. exact (fun h0 : term70 A h t => @lem1113618 A h t h1 h0). Qed.
Lemma lem1113620 {A : Type'} (h : A) (t : list A) (h1 : term70 A h t) : term70 A h t.
Proof. exact (h1). Qed.
Lemma lem1113621 {A : Type'} (h : A) (t : list A) (h1 : term68 A h t) (h2 : term70 A h t) : term68 A h t.
Proof. exact (@lem1113619 A h t h1 (@lem1113620 A h t h2)). Qed.
Lemma lem1113622 {A : Type'} (h : A) (t : list A) (h1 : term70 A h t) : term70 A h t.
Proof. exact (fun h0 : term68 A h t => @lem1113621 A h t h0 h1). Qed.
Lemma lem1113623 {A : Type'} (h : A) (t : list A) : term72 A h t.
Proof. exact (fun h0 : term70 A h t => @lem1113622 A h t h0). Qed.
Lemma lem1113626 {A : Type'} (h : A) (t : list A) : term70 A h t.
Proof. exact (@lem1113623 A h t (@lem1113615 A h t)). Qed.
Lemma lem1113627 {A : Type'} (h : A) (t : list A) : term70 A h t.
Proof. exact (@lem1113626 A h t). Qed.
Lemma lem1113637 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1113638 {A : Type'} (h : A) (t : list A) : (term68 A h t) = (term73 A h t).
Proof. exact (@lem1113637 (term69 A h t)). Qed.
Lemma lem1113640 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1113641 {A : Type'} (h : A) (t : list A) : (term73 A h t) = (term65 A h t).
Proof. exact (@lem1113640 (term65 A h t)). Qed.
Lemma lem1113646 {A : Type'} (h : A) (t : list A) : (term68 A h t) = (term65 A h t).
Proof. exact (TRANS (@lem1113638 A h t) (@lem1113641 A h t)). Qed.
Lemma lem1113648 {A : Type'} (P : Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1113649 {A : Type'} (P : Prop) (Q : type1143 A) : (term77 A P Q) = (term78 A P Q).
Proof. exact (@lem1113648 (list A) P Q). Qed.
Lemma lem1113650 {A : Type'} (h : A) (h' : A) (t : list A) : (term79 A h h' t) = (term80 A h h' t).
Proof. exact (@lem1113649 A (h = h') (term81 A t)). Qed.
Lemma lem1113651 {A : Type'} (t : list A) (t' : list A) : (term82 A t t') = (t = t').
Proof. exact (eq_refl (term82 A t t')). Qed.
Lemma lem1113652 {A : Type'} (h : A) (h' : A) : (term83 A h h') = (term83 A h h').
Proof. exact (eq_refl (term83 A h h')). Qed.
Lemma lem1113653 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term84 A h h' t t') = (term14 A h h' t t').
Proof. exact (MK_COMB (@lem1113652 A h h') (@lem1113651 A t t')). Qed.
Lemma lem1113654 {A : Type'} (h : A) (h' : A) (t : list A) : (term85 A h h' t) = (term59 A h h' t).
Proof. exact (fun_ext (fun t' : list A => @lem1113653 A h h' t t')). Qed.
Lemma lem1113655 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113656 {A : Type'} (h : A) (h' : A) (t : list A) : (term79 A h h' t) = (term61 A h h' t).
Proof. exact (MK_COMB (@lem1113655 A) (@lem1113654 A h h' t)). Qed.
Lemma lem1113657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113658 {A : Type'} (h : A) (h' : A) (t : list A) : (term86 A h h' t) = (term87 A h h' t).
Proof. exact (MK_COMB (@lem1113657) (@lem1113656 A h h' t)). Qed.
Lemma lem1113659 {A : Type'} (t : list A) (t' : list A) : (term82 A t t') = (t = t').
Proof. exact (eq_refl (term82 A t t')). Qed.
Lemma lem1113660 {A : Type'} (t : list A) : (term88 A t) = (term81 A t).
Proof. exact (fun_ext (fun t' : list A => @lem1113659 A t t')). Qed.
Lemma lem1113661 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113662 {A : Type'} (t : list A) : (term89 A t) = (term90 A t).
Proof. exact (MK_COMB (@lem1113661 A) (@lem1113660 A t)). Qed.
Lemma lem1113663 {A : Type'} (h : A) (h' : A) : (term83 A h h') = (term83 A h h').
Proof. exact (eq_refl (term83 A h h')). Qed.
Lemma lem1113664 {A : Type'} (h : A) (h' : A) (t : list A) : (term80 A h h' t) = (term91 A h h' t).
Proof. exact (MK_COMB (@lem1113663 A h h') (@lem1113662 A t)). Qed.
Lemma lem1113665 {A : Type'} (h : A) (h' : A) (t : list A) : ((term79 A h h' t) = (term80 A h h' t)) = ((term61 A h h' t) = (term91 A h h' t)).
Proof. exact (MK_COMB (@lem1113658 A h h' t) (@lem1113664 A h h' t)). Qed.
Lemma lem1113666 {A : Type'} (h : A) (h' : A) (t : list A) : (term61 A h h' t) = (term91 A h h' t).
Proof. exact (EQ_MP (@lem1113665 A h h' t) (@lem1113650 A h h' t)). Qed.
Lemma lem1113673 {A : Type'} (h : A) (t : list A) : (term63 A h t) = (term92 A h t).
Proof. exact (fun_ext (fun h' : A => @lem1113666 A h h' t)). Qed.
Lemma lem1113674 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113675 {A : Type'} (h : A) (t : list A) : (term65 A h t) = (term93 A h t).
Proof. exact (MK_COMB (@lem1113674 A) (@lem1113673 A h t)). Qed.
Lemma lem1113697 {A : Type'} (P : A -> Prop) (Q : Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem1113698 {A : Type'} (P : A -> Prop) (Q : Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (@lem1113697 A P Q). Qed.
Lemma lem1113699 {A : Type'} (h : A) (t : list A) : (term96 A h t) = (term97 A h t).
Proof. exact (@lem1113698 A (term98 A h) (term90 A t)). Qed.
Lemma lem1113700 {A : Type'} (h : A) (h' : A) : (term99 A h h') = (h = h').
Proof. exact (eq_refl (term99 A h h')). Qed.
Lemma lem1113701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113702 {A : Type'} (h : A) (h' : A) : (term100 A h h') = (term83 A h h').
Proof. exact (MK_COMB (@lem1113701) (@lem1113700 A h h')). Qed.
Lemma lem1113703 {A : Type'} (t : list A) : (term90 A t) = (term90 A t).
Proof. exact (eq_refl (term90 A t)). Qed.
Lemma lem1113704 {A : Type'} (h : A) (h' : A) (t : list A) : (term101 A h h' t) = (term91 A h h' t).
Proof. exact (MK_COMB (@lem1113702 A h h') (@lem1113703 A t)). Qed.
Lemma lem1113705 {A : Type'} (h : A) (t : list A) : (term102 A h t) = (term92 A h t).
Proof. exact (fun_ext (fun h' : A => @lem1113704 A h h' t)). Qed.
Lemma lem1113706 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113707 {A : Type'} (h : A) (t : list A) : (term96 A h t) = (term93 A h t).
Proof. exact (MK_COMB (@lem1113706 A) (@lem1113705 A h t)). Qed.
Lemma lem1113708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113709 {A : Type'} (h : A) (t : list A) : (term103 A h t) = (term104 A h t).
Proof. exact (MK_COMB (@lem1113708) (@lem1113707 A h t)). Qed.
Lemma lem1113710 {A : Type'} (h : A) (h' : A) : (term99 A h h') = (h = h').
Proof. exact (eq_refl (term99 A h h')). Qed.
Lemma lem1113711 {A : Type'} (h : A) : (term105 A h) = (term98 A h).
Proof. exact (fun_ext (fun h' : A => @lem1113710 A h h')). Qed.
Lemma lem1113712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113713 {A : Type'} (h : A) : (term106 A h) = (term107 A h).
Proof. exact (MK_COMB (@lem1113712 A) (@lem1113711 A h)). Qed.
Lemma lem1113714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113715 {A : Type'} (h : A) : (term108 A h) = (term109 A h).
Proof. exact (MK_COMB (@lem1113714) (@lem1113713 A h)). Qed.
Lemma lem1113716 {A : Type'} (t : list A) : (term90 A t) = (term90 A t).
Proof. exact (eq_refl (term90 A t)). Qed.
Lemma lem1113717 {A : Type'} (h : A) (t : list A) : (term97 A h t) = (term110 A h t).
Proof. exact (MK_COMB (@lem1113715 A h) (@lem1113716 A t)). Qed.
Lemma lem1113718 {A : Type'} (h : A) (t : list A) : ((term96 A h t) = (term97 A h t)) = ((term93 A h t) = (term110 A h t)).
Proof. exact (MK_COMB (@lem1113709 A h t) (@lem1113717 A h t)). Qed.
Lemma lem1113719 {A : Type'} (h : A) (t : list A) : (term93 A h t) = (term110 A h t).
Proof. exact (EQ_MP (@lem1113718 A h t) (@lem1113699 A h t)). Qed.
Lemma lem1113730 {A : Type'} (h : A) (t : list A) : (term65 A h t) = (term110 A h t).
Proof. exact (TRANS (@lem1113675 A h t) (@lem1113719 A h t)). Qed.
Lemma lem1113731 {A : Type'} (h : A) (t : list A) : (term68 A h t) = (term110 A h t).
Proof. exact (TRANS (@lem1113646 A h t) (@lem1113730 A h t)). Qed.
Lemma lem1113732 {A : Type'} (t : list A) : (term111 A t) = (term112 A t).
Proof. exact (fun_ext (fun h : A => @lem1113731 A h t)). Qed.
Lemma lem1113733 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113734 {A : Type'} (t : list A) : (term113 A t) = (term114 A t).
Proof. exact (MK_COMB (@lem1113733 A) (@lem1113732 A t)). Qed.
Lemma lem1113736 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1113737 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (@lem1113736 A P Q). Qed.
Lemma lem1113738 {A : Type'} (t : list A) : (term117 A t) = (term118 A t).
Proof. exact (@lem1113737 A (term119 A) (term120 A t)). Qed.
Lemma lem1113739 {A : Type'} (h : A) : (term121 A h) = (term107 A h).
Proof. exact (eq_refl (term121 A h)). Qed.
Lemma lem1113740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113741 {A : Type'} (h : A) : (term122 A h) = (term109 A h).
Proof. exact (MK_COMB (@lem1113740) (@lem1113739 A h)). Qed.
Lemma lem1113742 {A : Type'} (h : A) (t : list A) : (term123 A t h) = (term90 A t).
Proof. exact (eq_refl (term123 A t h)). Qed.
Lemma lem1113743 {A : Type'} (h : A) (t : list A) : (term124 A t h) = (term110 A h t).
Proof. exact (MK_COMB (@lem1113741 A h) (@lem1113742 A h t)). Qed.
Lemma lem1113744 {A : Type'} (t : list A) : (term125 A t) = (term112 A t).
Proof. exact (fun_ext (fun h : A => @lem1113743 A h t)). Qed.
Lemma lem1113745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113746 {A : Type'} (t : list A) : (term117 A t) = (term114 A t).
Proof. exact (MK_COMB (@lem1113745 A) (@lem1113744 A t)). Qed.
Lemma lem1113747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113748 {A : Type'} (t : list A) : (term126 A t) = (term127 A t).
Proof. exact (MK_COMB (@lem1113747) (@lem1113746 A t)). Qed.
Lemma lem1113749 {A : Type'} (h : A) : (term121 A h) = (term107 A h).
Proof. exact (eq_refl (term121 A h)). Qed.
Lemma lem1113750 {A : Type'} : (term128 A) = (term119 A).
Proof. exact (fun_ext (fun h : A => @lem1113749 A h)). Qed.
Lemma lem1113751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113752 {A : Type'} : (term129 A) = (term130 A).
Proof. exact (MK_COMB (@lem1113751 A) (@lem1113750 A)). Qed.
Lemma lem1113753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113754 {A : Type'} : (term131 A) = (term132 A).
Proof. exact (MK_COMB (@lem1113753) (@lem1113752 A)). Qed.
Lemma lem1113755 {A : Type'} (h : A) (t : list A) : (term123 A t h) = (term90 A t).
Proof. exact (eq_refl (term123 A t h)). Qed.
Lemma lem1113756 {A : Type'} (t : list A) : (term133 A t) = (term120 A t).
Proof. exact (fun_ext (fun h : A => @lem1113755 A h t)). Qed.
Lemma lem1113757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113758 {A : Type'} (t : list A) : (term134 A t) = (term135 A t).
Proof. exact (MK_COMB (@lem1113757 A) (@lem1113756 A t)). Qed.
Lemma lem1113759 {A : Type'} (t : list A) : (term118 A t) = (term136 A t).
Proof. exact (MK_COMB (@lem1113754 A) (@lem1113758 A t)). Qed.
Lemma lem1113760 {A : Type'} (t : list A) : ((term117 A t) = (term118 A t)) = ((term114 A t) = (term136 A t)).
Proof. exact (MK_COMB (@lem1113748 A t) (@lem1113759 A t)). Qed.
Lemma lem1113761 {A : Type'} (t : list A) : (term114 A t) = (term136 A t).
Proof. exact (EQ_MP (@lem1113760 A t) (@lem1113738 A t)). Qed.
Lemma lem1113773 {A : Type'} (t : Prop) : (term137 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1113774 {A : Type'} (t : Prop) : (term137 A t) = t.
Proof. exact (@lem1113773 A t). Qed.
Lemma lem1113775 {A : Type'} (t : list A) : (term135 A t) = (term90 A t).
Proof. exact (@lem1113774 A (term90 A t)). Qed.
Lemma lem1113780 {A : Type'} : (term132 A) = (term132 A).
Proof. exact (eq_refl (term132 A)). Qed.
Lemma lem1113781 {A : Type'} (t : list A) : (term136 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem1113780 A) (@lem1113775 A t)). Qed.
Lemma lem1113784 {A : Type'} (t : list A) : (term114 A t) = (term138 A t).
Proof. exact (TRANS (@lem1113761 A t) (@lem1113781 A t)). Qed.
Lemma lem1113785 {A : Type'} (t : list A) : (term113 A t) = (term138 A t).
Proof. exact (TRANS (@lem1113734 A t) (@lem1113784 A t)). Qed.
Lemma lem1113786 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (fun_ext (fun t : list A => @lem1113785 A t)). Qed.
Lemma lem1113787 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113788 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (MK_COMB (@lem1113787 A) (@lem1113786 A)). Qed.
Lemma lem1113790 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1113791 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term143 A P Q) = (term144 A P Q).
Proof. exact (@lem1113790 (list A) P Q). Qed.
Lemma lem1113792 {A : Type'} : (term145 A) = (term146 A).
Proof. exact (@lem1113791 A (term147 A) (term148 A)). Qed.
Lemma lem1113793 {A : Type'} (t : list A) : (term149 A t) = (term130 A).
Proof. exact (eq_refl (term149 A t)). Qed.
Lemma lem1113794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113795 {A : Type'} (t : list A) : (term150 A t) = (term132 A).
Proof. exact (MK_COMB (@lem1113794) (@lem1113793 A t)). Qed.
Lemma lem1113796 {A : Type'} (t : list A) : (term151 A t) = (term90 A t).
Proof. exact (eq_refl (term151 A t)). Qed.
Lemma lem1113797 {A : Type'} (t : list A) : (term152 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem1113795 A t) (@lem1113796 A t)). Qed.
Lemma lem1113798 {A : Type'} : (term153 A) = (term140 A).
Proof. exact (fun_ext (fun t : list A => @lem1113797 A t)). Qed.
Lemma lem1113799 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113800 {A : Type'} : (term145 A) = (term142 A).
Proof. exact (MK_COMB (@lem1113799 A) (@lem1113798 A)). Qed.
Lemma lem1113801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113802 {A : Type'} : (term154 A) = (term155 A).
Proof. exact (MK_COMB (@lem1113801) (@lem1113800 A)). Qed.
Lemma lem1113803 {A : Type'} (t : list A) : (term149 A t) = (term130 A).
Proof. exact (eq_refl (term149 A t)). Qed.
Lemma lem1113804 {A : Type'} : (term156 A) = (term147 A).
Proof. exact (fun_ext (fun t : list A => @lem1113803 A t)). Qed.
Lemma lem1113805 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113806 {A : Type'} : (term157 A) = (term158 A).
Proof. exact (MK_COMB (@lem1113805 A) (@lem1113804 A)). Qed.
Lemma lem1113807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113808 {A : Type'} : (term159 A) = (term160 A).
Proof. exact (MK_COMB (@lem1113807) (@lem1113806 A)). Qed.
Lemma lem1113809 {A : Type'} (t : list A) : (term151 A t) = (term90 A t).
Proof. exact (eq_refl (term151 A t)). Qed.
Lemma lem1113810 {A : Type'} : (term161 A) = (term148 A).
Proof. exact (fun_ext (fun t : list A => @lem1113809 A t)). Qed.
Lemma lem1113811 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113812 {A : Type'} : (term162 A) = (term163 A).
Proof. exact (MK_COMB (@lem1113811 A) (@lem1113810 A)). Qed.
Lemma lem1113813 {A : Type'} : (term146 A) = (term164 A).
Proof. exact (MK_COMB (@lem1113808 A) (@lem1113812 A)). Qed.
Lemma lem1113814 {A : Type'} : ((term145 A) = (term146 A)) = ((term142 A) = (term164 A)).
Proof. exact (MK_COMB (@lem1113802 A) (@lem1113813 A)). Qed.
Lemma lem1113815 {A : Type'} : (term142 A) = (term164 A).
Proof. exact (EQ_MP (@lem1113814 A) (@lem1113792 A)). Qed.
Lemma lem1113819 {A : Type'} (t : Prop) : (term137 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1113820 {A : Type'} (t : Prop) : (term165 A t) = t.
Proof. exact (@lem1113819 (list A) t). Qed.
Lemma lem1113821 {A : Type'} : (term158 A) = (term130 A).
Proof. exact (@lem1113820 A (term130 A)). Qed.
Lemma lem1113830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113831 {A : Type'} : (term160 A) = (term132 A).
Proof. exact (MK_COMB (@lem1113830) (@lem1113821 A)). Qed.
Lemma lem1113840 {A : Type'} : (term163 A) = (term163 A).
Proof. exact (eq_refl (term163 A)). Qed.
Lemma lem1113841 {A : Type'} : (term164 A) = (term166 A).
Proof. exact (MK_COMB (@lem1113831 A) (@lem1113840 A)). Qed.
Lemma lem1113844 {A : Type'} : (term142 A) = (term166 A).
Proof. exact (TRANS (@lem1113815 A) (@lem1113841 A)). Qed.
Lemma lem1113849 {A : Type'} : (term141 A) = (term166 A).
Proof. exact (TRANS (@lem1113788 A) (@lem1113844 A)). Qed.
Lemma lem1113850 {A : Type'} (t : list A) (t' : list A) : (t = t') = (t = t').
Proof. exact (eq_refl (t = t')). Qed.
Lemma lem1113851 {A : Type'} (t : list A) : (term81 A t) = (term81 A t).
Proof. exact (fun_ext (fun t' : list A => @lem1113850 A t t')). Qed.
Lemma lem1113852 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113853 {A : Type'} (t : list A) : (term90 A t) = (term90 A t).
Proof. exact (MK_COMB (@lem1113852 A) (@lem1113851 A t)). Qed.
Lemma lem1113854 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (fun_ext (fun t : list A => @lem1113853 A t)). Qed.
Lemma lem1113855 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113856 {A : Type'} : (term163 A) = (term163 A).
Proof. exact (MK_COMB (@lem1113855 A) (@lem1113854 A)). Qed.
Lemma lem1113857 {A : Type'} (h : A) (h' : A) : (h = h') = (h = h').
Proof. exact (eq_refl (h = h')). Qed.
Lemma lem1113858 {A : Type'} (h : A) : (term98 A h) = (term98 A h).
Proof. exact (fun_ext (fun h' : A => @lem1113857 A h h')). Qed.
Lemma lem1113859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113860 {A : Type'} (h : A) : (term107 A h) = (term107 A h).
Proof. exact (MK_COMB (@lem1113859 A) (@lem1113858 A h)). Qed.
Lemma lem1113861 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (fun_ext (fun h : A => @lem1113860 A h)). Qed.
Lemma lem1113862 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113863 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (MK_COMB (@lem1113862 A) (@lem1113861 A)). Qed.
Lemma lem1113864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113865 {A : Type'} : (term132 A) = (term132 A).
Proof. exact (MK_COMB (@lem1113864) (@lem1113863 A)). Qed.
Lemma lem1113866 {A : Type'} : (term166 A) = (term166 A).
Proof. exact (MK_COMB (@lem1113865 A) (@lem1113856 A)). Qed.
Lemma lem1113895 {A : Type'} : (term141 A) = (term166 A).
Proof. exact (TRANS (@lem1113849 A) (@lem1113866 A)). Qed.
Lemma lem1113896 {A : Type'} : (term166 A) = (term141 A).
Proof. exact (SYM (@lem1113895 A)). Qed.
Lemma lem1113898 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1113899 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (@lem1113898 (term166 A)). Qed.
Lemma lem1113900 {A : Type'} : (term167 A) = (term166 A).
Proof. exact (SYM (@lem1113899 A)). Qed.
Lemma lem1113901 {A : Type'} (h1 : term168 A) : term168 A.
Proof. exact (h1). Qed.
Lemma lem1113903 {A : Type'} (P : A -> Prop) : (term169 A P) = (term170 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem1113904 {A : Type'} (h : A) : (term171 A h) = (term172 A h).
Proof. exact (@lem1113903 A (term98 A h)). Qed.
Lemma lem1113905 {A : Type'} (h : A) (h' : A) : (term99 A h h') = (h = h').
Proof. exact (eq_refl (term99 A h h')). Qed.
Lemma lem1113906 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1113908 {A : Type'} (h : A) (h' : A) : (term173 A h h') = (term174 A h h').
Proof. exact (MK_COMB (@lem1113906) (@lem1113905 A h h')). Qed.
Lemma lem1113909 {A : Type'} (h : A) : (term175 A h) = (term176 A h).
Proof. exact (fun_ext (fun h' : A => @lem1113908 A h h')). Qed.
Lemma lem1113910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1113911 {A : Type'} (h : A) : (term172 A h) = (term177 A h).
Proof. exact (MK_COMB (@lem1113910 A) (@lem1113909 A h)). Qed.
Lemma lem1113912 {A : Type'} (h : A) : (term171 A h) = (term177 A h).
Proof. exact (TRANS (@lem1113904 A h) (@lem1113911 A h)). Qed.
Lemma lem1113913 {A : Type'} (P : A -> Prop) : (term178 A P) = (term179 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1113914 {A : Type'} : (term180 A) = (term181 A).
Proof. exact (@lem1113913 A (term119 A)). Qed.
Lemma lem1113915 {A : Type'} (h : A) : (term121 A h) = (term107 A h).
Proof. exact (eq_refl (term121 A h)). Qed.
Lemma lem1113916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1113917 {A : Type'} (h : A) : (term182 A h) = (term171 A h).
Proof. exact (MK_COMB (@lem1113916) (@lem1113915 A h)). Qed.
Lemma lem1113918 {A : Type'} (h : A) : (term182 A h) = (term177 A h).
Proof. exact (TRANS (@lem1113917 A h) (@lem1113912 A h)). Qed.
Lemma lem1113919 {A : Type'} : (term183 A) = (term184 A).
Proof. exact (fun_ext (fun h : A => @lem1113918 A h)). Qed.
Lemma lem1113920 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113921 {A : Type'} : (term181 A) = (term185 A).
Proof. exact (MK_COMB (@lem1113920 A) (@lem1113919 A)). Qed.
Lemma lem1113922 {A : Type'} : (term180 A) = (term185 A).
Proof. exact (TRANS (@lem1113914 A) (@lem1113921 A)). Qed.
Lemma lem1113924 {A : Type'} (P : type1143 A) : (term186 A P) = (term187 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1113925 {A : Type'} (t : list A) : (term188 A t) = (term189 A t).
Proof. exact (@lem1113924 A (term81 A t)). Qed.
Lemma lem1113926 {A : Type'} (t : list A) (t' : list A) : (term82 A t t') = (t = t').
Proof. exact (eq_refl (term82 A t t')). Qed.
Lemma lem1113927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1113929 {A : Type'} (t : list A) (t' : list A) : (term190 A t t') = (term191 A t t').
Proof. exact (MK_COMB (@lem1113927) (@lem1113926 A t t')). Qed.
Lemma lem1113930 {A : Type'} (t : list A) : (term192 A t) = (term193 A t).
Proof. exact (fun_ext (fun t' : list A => @lem1113929 A t t')). Qed.
Lemma lem1113931 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1113932 {A : Type'} (t : list A) : (term189 A t) = (term194 A t).
Proof. exact (MK_COMB (@lem1113931 A) (@lem1113930 A t)). Qed.
Lemma lem1113933 {A : Type'} (t : list A) : (term188 A t) = (term194 A t).
Proof. exact (TRANS (@lem1113925 A t) (@lem1113932 A t)). Qed.
Lemma lem1113934 {A : Type'} (P : type1143 A) : (term195 A P) = (term196 A P).
Proof. exact (@lem18392 (list A) P). Qed.
Lemma lem1113935 {A : Type'} : (term197 A) = (term198 A).
Proof. exact (@lem1113934 A (term148 A)). Qed.
Lemma lem1113936 {A : Type'} (t : list A) : (term151 A t) = (term90 A t).
Proof. exact (eq_refl (term151 A t)). Qed.
Lemma lem1113937 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1113938 {A : Type'} (t : list A) : (term199 A t) = (term188 A t).
Proof. exact (MK_COMB (@lem1113937) (@lem1113936 A t)). Qed.
Lemma lem1113939 {A : Type'} (t : list A) : (term199 A t) = (term194 A t).
Proof. exact (TRANS (@lem1113938 A t) (@lem1113933 A t)). Qed.
Lemma lem1113940 {A : Type'} : (term200 A) = (term201 A).
Proof. exact (fun_ext (fun t : list A => @lem1113939 A t)). Qed.
Lemma lem1113941 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113942 {A : Type'} : (term198 A) = (term202 A).
Proof. exact (MK_COMB (@lem1113941 A) (@lem1113940 A)). Qed.
Lemma lem1113943 {A : Type'} : (term197 A) = (term202 A).
Proof. exact (TRANS (@lem1113935 A) (@lem1113942 A)). Qed.
Lemma lem1113944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1113945 {A : Type'} : (term203 A) = (term204 A).
Proof. exact (MK_COMB (@lem1113944) (@lem1113922 A)). Qed.
Lemma lem1113946 {A : Type'} : (term205 A) = (term206 A).
Proof. exact (MK_COMB (@lem1113945 A) (@lem1113943 A)). Qed.
Lemma lem1113947 {A : Type'} : (term168 A) = (term205 A).
Proof. exact (@lem17045 (term130 A) (term163 A)). Qed.
Lemma lem1113948 {A : Type'} : (term168 A) = (term206 A).
Proof. exact (TRANS (@lem1113947 A) (@lem1113946 A)). Qed.
Lemma lem1113969 {A : Type'} (P : A -> Prop) (Q : Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1113970 {A : Type'} (P : A -> Prop) (Q : Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (@lem1113969 A P Q). Qed.
Lemma lem1113971 {A : Type'} : (term209 A) = (term210 A).
Proof. exact (@lem1113970 A (term184 A) (term202 A)). Qed.
Lemma lem1113972 {A : Type'} (h : A) : (term211 A h) = (term177 A h).
Proof. exact (eq_refl (term211 A h)). Qed.
Lemma lem1113973 {A : Type'} : (term212 A) = (term184 A).
Proof. exact (fun_ext (fun h : A => @lem1113972 A h)). Qed.
Lemma lem1113974 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113975 {A : Type'} : (term213 A) = (term185 A).
Proof. exact (MK_COMB (@lem1113974 A) (@lem1113973 A)). Qed.
Lemma lem1113976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1113977 {A : Type'} : (term214 A) = (term204 A).
Proof. exact (MK_COMB (@lem1113976) (@lem1113975 A)). Qed.
Lemma lem1113978 {A : Type'} : (term202 A) = (term202 A).
Proof. exact (eq_refl (term202 A)). Qed.
Lemma lem1113979 {A : Type'} : (term209 A) = (term206 A).
Proof. exact (MK_COMB (@lem1113977 A) (@lem1113978 A)). Qed.
Lemma lem1113980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113981 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (MK_COMB (@lem1113980) (@lem1113979 A)). Qed.
Lemma lem1113982 {A : Type'} (h : A) : (term211 A h) = (term177 A h).
Proof. exact (eq_refl (term211 A h)). Qed.
Lemma lem1113983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1113984 {A : Type'} (h : A) : (term217 A h) = (term218 A h).
Proof. exact (MK_COMB (@lem1113983) (@lem1113982 A h)). Qed.
Lemma lem1113985 {A : Type'} : (term202 A) = (term202 A).
Proof. exact (eq_refl (term202 A)). Qed.
Lemma lem1113986 {A : Type'} (h : A) : (term219 A h) = (term220 A h).
Proof. exact (MK_COMB (@lem1113984 A h) (@lem1113985 A)). Qed.
Lemma lem1113987 {A : Type'} : (term221 A) = (term222 A).
Proof. exact (fun_ext (fun h : A => @lem1113986 A h)). Qed.
Lemma lem1113988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1113989 {A : Type'} : (term210 A) = (term223 A).
Proof. exact (MK_COMB (@lem1113988 A) (@lem1113987 A)). Qed.
Lemma lem1113990 {A : Type'} : ((term209 A) = (term210 A)) = ((term206 A) = (term223 A)).
Proof. exact (MK_COMB (@lem1113981 A) (@lem1113989 A)). Qed.
Lemma lem1113991 {A : Type'} : (term206 A) = (term223 A).
Proof. exact (EQ_MP (@lem1113990 A) (@lem1113971 A)). Qed.
Lemma lem1113993 {A : Type'} (P : Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1113994 {A : Type'} (P : Prop) (Q : type1143 A) : (term226 A P Q) = (term227 A P Q).
Proof. exact (@lem1113993 (list A) P Q). Qed.
Lemma lem1113995 {A : Type'} (h : A) : (term228 A h) = (term229 A h).
Proof. exact (@lem1113994 A (term177 A h) (term201 A)). Qed.
Lemma lem1113996 {A : Type'} (t : list A) : (term230 A t) = (term194 A t).
Proof. exact (eq_refl (term230 A t)). Qed.
Lemma lem1113997 {A : Type'} : (term231 A) = (term201 A).
Proof. exact (fun_ext (fun t : list A => @lem1113996 A t)). Qed.
Lemma lem1113998 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1113999 {A : Type'} : (term232 A) = (term202 A).
Proof. exact (MK_COMB (@lem1113998 A) (@lem1113997 A)). Qed.
Lemma lem1114000 {A : Type'} (h : A) : (term218 A h) = (term218 A h).
Proof. exact (eq_refl (term218 A h)). Qed.
Lemma lem1114001 {A : Type'} (h : A) : (term228 A h) = (term220 A h).
Proof. exact (MK_COMB (@lem1114000 A h) (@lem1113999 A)). Qed.
Lemma lem1114002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114003 {A : Type'} (h : A) : (term233 A h) = (term234 A h).
Proof. exact (MK_COMB (@lem1114002) (@lem1114001 A h)). Qed.
Lemma lem1114004 {A : Type'} (t : list A) : (term230 A t) = (term194 A t).
Proof. exact (eq_refl (term230 A t)). Qed.
Lemma lem1114005 {A : Type'} (h : A) : (term218 A h) = (term218 A h).
Proof. exact (eq_refl (term218 A h)). Qed.
Lemma lem1114006 {A : Type'} (h : A) (t : list A) : (term235 A h t) = (term236 A h t).
Proof. exact (MK_COMB (@lem1114005 A h) (@lem1114004 A t)). Qed.
Lemma lem1114007 {A : Type'} (h : A) : (term237 A h) = (term238 A h).
Proof. exact (fun_ext (fun t : list A => @lem1114006 A h t)). Qed.
Lemma lem1114008 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1114009 {A : Type'} (h : A) : (term229 A h) = (term239 A h).
Proof. exact (MK_COMB (@lem1114008 A) (@lem1114007 A h)). Qed.
Lemma lem1114010 {A : Type'} (h : A) : ((term228 A h) = (term229 A h)) = ((term220 A h) = (term239 A h)).
Proof. exact (MK_COMB (@lem1114003 A h) (@lem1114009 A h)). Qed.
Lemma lem1114011 {A : Type'} (h : A) : (term220 A h) = (term239 A h).
Proof. exact (EQ_MP (@lem1114010 A h) (@lem1113995 A h)). Qed.
Lemma lem1114012 {A : Type'} : (term222 A) = (term240 A).
Proof. exact (fun_ext (fun h : A => @lem1114011 A h)). Qed.
Lemma lem1114013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1114014 {A : Type'} : (term223 A) = (term241 A).
Proof. exact (MK_COMB (@lem1114013 A) (@lem1114012 A)). Qed.
Lemma lem1114016 {A : Type'} : (term206 A) = (term241 A).
Proof. exact (TRANS (@lem1113991 A) (@lem1114014 A)). Qed.
Lemma lem1114017 {A : Type'} : (term168 A) = (term241 A).
Proof. exact (TRANS (@lem1113948 A) (@lem1114016 A)). Qed.
Lemma lem1114018 {A : Type'} (h1 : term168 A) : term241 A.
Proof. exact (EQ_MP (@lem1114017 A) (@lem1113901 A h1)). Qed.
Lemma lem1114019 {A : Type'} (h : A) (h1 : term239 A h) : term239 A h.
Proof. exact (h1). Qed.
Lemma lem1114020 {A : Type'} (h : A) (t : list A) (h1 : term236 A h t) : term236 A h t.
Proof. exact (h1). Qed.
Lemma lem1114027 {A : Type'} (t : list A) (t' : list A) : (term191 A t t') = (term191 A t t').
Proof. exact (eq_refl (term191 A t t')). Qed.
Lemma lem1114028 {A : Type'} (t : list A) : (term193 A t) = (term193 A t).
Proof. exact (fun_ext (fun t' : list A => @lem1114027 A t t')). Qed.
Lemma lem1114029 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1114030 {A : Type'} (t : list A) : (term194 A t) = (term194 A t).
Proof. exact (MK_COMB (@lem1114029 A) (@lem1114028 A t)). Qed.
Lemma lem1114037 {A : Type'} (h : A) (h' : A) : (term174 A h h') = (term174 A h h').
Proof. exact (eq_refl (term174 A h h')). Qed.
Lemma lem1114038 {A : Type'} (h : A) : (term176 A h) = (term176 A h).
Proof. exact (fun_ext (fun h' : A => @lem1114037 A h h')). Qed.
Lemma lem1114039 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1114040 {A : Type'} (h : A) : (term177 A h) = (term177 A h).
Proof. exact (MK_COMB (@lem1114039 A) (@lem1114038 A h)). Qed.
Lemma lem1114041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114042 {A : Type'} (h : A) : (term218 A h) = (term218 A h).
Proof. exact (MK_COMB (@lem1114041) (@lem1114040 A h)). Qed.
Lemma lem1114043 {A : Type'} (h : A) (t : list A) : (term236 A h t) = (term236 A h t).
Proof. exact (MK_COMB (@lem1114042 A h) (@lem1114030 A t)). Qed.
Lemma lem1114044 {A : Type'} (h : A) (t : list A) (h1 : term236 A h t) : term236 A h t.
Proof. exact (EQ_MP (@lem1114043 A h t) (@lem1114020 A h t h1)). Qed.
Lemma lem1114045 {A : Type'} (h : A) (h1 : term177 A h) : term177 A h.
Proof. exact (h1). Qed.
Lemma lem1114046 {A : Type'} (t : list A) (h1 : term194 A t) : term194 A t.
Proof. exact (h1). Qed.
Lemma lem1114048 {A : Type'} (h : A) (h' : A) : (term174 A h h') = (term174 A h h').
Proof. exact (eq_refl (term174 A h h')). Qed.
Lemma lem1114049 {A : Type'} (h : A) : (term176 A h) = (term176 A h).
Proof. exact (fun_ext (fun h' : A => @lem1114048 A h h')). Qed.
Lemma lem1114050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1114052 {A : Type'} (h : A) : (term177 A h) = (term177 A h).
Proof. exact (MK_COMB (@lem1114050 A) (@lem1114049 A h)). Qed.
Lemma lem1114053 {A : Type'} (h : A) (h1 : term177 A h) : term177 A h.
Proof. exact (EQ_MP (@lem1114052 A h) (@lem1114045 A h h1)). Qed.
Lemma lem1114055 {A : Type'} (t : list A) (t' : list A) : (term191 A t t') = (term191 A t t').
Proof. exact (eq_refl (term191 A t t')). Qed.
Lemma lem1114056 {A : Type'} (t : list A) : (term193 A t) = (term193 A t).
Proof. exact (fun_ext (fun t' : list A => @lem1114055 A t t')). Qed.
Lemma lem1114057 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1114059 {A : Type'} (t : list A) : (term194 A t) = (term194 A t).
Proof. exact (MK_COMB (@lem1114057 A) (@lem1114056 A t)). Qed.
Lemma lem1114060 {A : Type'} (t : list A) (h1 : term194 A t) : term194 A t.
Proof. exact (EQ_MP (@lem1114059 A t) (@lem1114046 A t h1)). Qed.
Lemma lem1114061 {A : Type'} (_18111 : A) (h : A) (h1 : term177 A h) : term242 A h _18111.
Proof. exact (@lem1114053 A h h1 _18111). Qed.
Lemma lem1114062 {A : Type'} (h : A) (_18111 : A) : (term242 A h _18111) = (term174 A h _18111).
Proof. exact (eq_refl (term242 A h _18111)). Qed.
Lemma lem1114064 {A : Type'} (_18112 : list A) (t : list A) (h1 : term194 A t) : term243 A t _18112.
Proof. exact (@lem1114060 A t h1 _18112). Qed.
Lemma lem1114065 {A : Type'} (t : list A) (_18112 : list A) : (term243 A t _18112) = (term191 A t _18112).
Proof. exact (eq_refl (term243 A t _18112)). Qed.
Lemma lem1114068 {A : Type'} (_18111 : A) (h : A) (h1 : term177 A h) : term174 A h _18111.
Proof. exact (EQ_MP (@lem1114062 A h _18111) (@lem1114061 A _18111 h h1)). Qed.
Lemma lem1114070 {A : Type'} (_18112 : list A) (t : list A) (h1 : term194 A t) : term191 A t _18112.
Proof. exact (EQ_MP (@lem1114065 A t _18112) (@lem1114064 A _18112 t h1)). Qed.
Lemma lem1114074 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1114075 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1114074 A x). Qed.
Lemma lem1114076 {A : Type'} (h : A) : h = h.
Proof. exact (@lem1114075 A h). Qed.
Lemma lem1114077 {A : Type'} (h : A) : term244 A h.
Proof. exact (fun h0 : term245 A h => @lem1114076 A h). Qed.
Lemma lem1114079 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114080 {A : Type'} (h : A) : (term244 A h) = (h = h).
Proof. exact (@lem1114079 (h = h)). Qed.
Lemma lem1114081 {A : Type'} (h : A) : h = h.
Proof. exact (EQ_MP (@lem1114080 A h) (@lem1114077 A h)). Qed.
Lemma lem1114084 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1114086 {A : Type'} (h : A) (_18111 : A) : (term174 A h _18111) = (term247 A h _18111).
Proof. exact (@lem1114084 (h = _18111)). Qed.
Lemma lem1114089 {A : Type'} (_18111 : A) (h : A) (h1 : term177 A h) : term247 A h _18111.
Proof. exact (EQ_MP (@lem1114086 A h _18111) (@lem1114068 A _18111 h h1)). Qed.
Lemma lem1114090 {A : Type'} (_18111 : A) (h : A) (h1 : term177 A h) : term247 A h _18111.
Proof. exact (@lem1114089 A _18111 h h1). Qed.
Lemma lem1114091 {A : Type'} (h : A) (h1 : term177 A h) : term248 A h.
Proof. exact (@lem1114090 A h h h1). Qed.
Lemma lem1114094 {A : Type'} (h : A) (h1 : term177 A h) : False.
Proof. exact (@lem1114091 A h h1 (@lem1114081 A h)). Qed.
Lemma lem1114095 {A : Type'} (h : A) (h1 : term177 A h) : term249.
Proof. exact (fun h0 : ~ False => @lem1114094 A h h1). Qed.
Lemma lem1114097 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114098 : term249 = False.
Proof. exact (@lem1114097 False). Qed.
Lemma lem1114099 {A : Type'} (h : A) (h1 : term177 A h) : False.
Proof. exact (EQ_MP (@lem1114098) (@lem1114095 A h h1)). Qed.
Lemma lem1114103 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1114104 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1114103 A x). Qed.
Lemma lem1114105 {A : Type'} (t : list A) : t = t.
Proof. exact (@lem1114104 A t). Qed.
Lemma lem1114106 {A : Type'} (t : list A) : term250 A t.
Proof. exact (fun h0 : term251 A t => @lem1114105 A t). Qed.
Lemma lem1114108 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114109 {A : Type'} (t : list A) : (term250 A t) = (t = t).
Proof. exact (@lem1114108 (t = t)). Qed.
Lemma lem1114110 {A : Type'} (t : list A) : t = t.
Proof. exact (EQ_MP (@lem1114109 A t) (@lem1114106 A t)). Qed.
Lemma lem1114113 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1114115 {A : Type'} (t : list A) (_18112 : list A) : (term191 A t _18112) = (term252 A t _18112).
Proof. exact (@lem1114113 (t = _18112)). Qed.
Lemma lem1114118 {A : Type'} (_18112 : list A) (t : list A) (h1 : term194 A t) : term252 A t _18112.
Proof. exact (EQ_MP (@lem1114115 A t _18112) (@lem1114070 A _18112 t h1)). Qed.
Lemma lem1114119 {A : Type'} (_18112 : list A) (t : list A) (h1 : term194 A t) : term252 A t _18112.
Proof. exact (@lem1114118 A _18112 t h1). Qed.
Lemma lem1114120 {A : Type'} (t : list A) (h1 : term194 A t) : term253 A t.
Proof. exact (@lem1114119 A t t h1). Qed.
Lemma lem1114123 {A : Type'} (t : list A) (h1 : term194 A t) : False.
Proof. exact (@lem1114120 A t h1 (@lem1114110 A t)). Qed.
Lemma lem1114124 {A : Type'} (t : list A) (h1 : term194 A t) : term249.
Proof. exact (fun h0 : ~ False => @lem1114123 A t h1). Qed.
Lemma lem1114126 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114127 : term249 = False.
Proof. exact (@lem1114126 False). Qed.
Lemma lem1114128 {A : Type'} (t : list A) (h1 : term194 A t) : False.
Proof. exact (EQ_MP (@lem1114127) (@lem1114124 A t h1)). Qed.
Lemma lem1114129 {A : Type'} (t : list A) (h1 : term194 A t) : (term194 A t) = False.
Proof. exact (prop_ext (fun h2 : term194 A t => @lem1114128 A t h1) (fun h2 : False => @lem1114060 A t h1)). Qed.
Lemma lem1114130 {A : Type'} (t : list A) (h1 : term194 A t) : False.
Proof. exact (EQ_MP (@lem1114129 A t h1) (@lem1114060 A t h1)). Qed.
Lemma lem1114131 {A : Type'} (h : A) (h1 : term177 A h) : (term177 A h) = False.
Proof. exact (prop_ext (fun h2 : term177 A h => @lem1114099 A h h1) (fun h2 : False => @lem1114053 A h h1)). Qed.
Lemma lem1114132 {A : Type'} (h : A) (h1 : term177 A h) : False.
Proof. exact (EQ_MP (@lem1114131 A h h1) (@lem1114053 A h h1)). Qed.
Lemma lem1114133 {A : Type'} (h : A) (t : list A) (h1 : term236 A h t) : False.
Proof. exact (or_elim (@lem1114044 A h t h1) (fun h0 : term177 A h => @lem1114132 A h h0) (fun h0 : term194 A t => @lem1114130 A t h0)). Qed.
Lemma lem1114134 {A : Type'} (h : A) (t : list A) (h1 : term236 A h t) : (term236 A h t) = False.
Proof. exact (prop_ext (fun h2 : term236 A h t => @lem1114133 A h t h1) (fun h2 : False => @lem1114044 A h t h1)). Qed.
Lemma lem1114135 {A : Type'} (h : A) (t : list A) (h1 : term236 A h t) : False.
Proof. exact (EQ_MP (@lem1114134 A h t h1) (@lem1114044 A h t h1)). Qed.
Lemma lem1114136 {A : Type'} (h : A) (h1 : term239 A h) : False.
Proof. exact (ex_elim (@lem1114019 A h h1) (fun t : list A => fun h0 : term238 A h t => @lem1114135 A h t h0)). Qed.
Lemma lem1114137 {A : Type'} (h1 : term168 A) : False.
Proof. exact (ex_elim (@lem1114018 A h1) (fun h : A => fun h0 : term240 A h => @lem1114136 A h h0)). Qed.
Lemma lem1114138 {A : Type'} (h1 : term168 A) : (term168 A) = False.
Proof. exact (prop_ext (fun h2 : term168 A => @lem1114137 A h1) (fun h2 : False => @lem1113901 A h1)). Qed.
Lemma lem1114139 {A : Type'} (h1 : term168 A) : False.
Proof. exact (EQ_MP (@lem1114138 A h1) (@lem1113901 A h1)). Qed.
Lemma lem1114140 {A : Type'} : term167 A.
Proof. exact (fun h0 : term168 A => @lem1114139 A h0). Qed.
Lemma lem1114141 {A : Type'} : term166 A.
Proof. exact (EQ_MP (@lem1113900 A) (@lem1114140 A)). Qed.
Lemma lem1114142 {A : Type'} : term141 A.
Proof. exact (EQ_MP (@lem1113896 A) (@lem1114141 A)). Qed.
Lemma lem1114143 {A : Type'} (t : list A) : term254 A t.
Proof. exact (@lem1114142 A t). Qed.
Lemma lem1114144 {A : Type'} (t : list A) : (term254 A t) = (term113 A t).
Proof. exact (eq_refl (term254 A t)). Qed.
Lemma lem1114145 {A : Type'} (t : list A) : term113 A t.
Proof. exact (EQ_MP (@lem1114144 A t) (@lem1114143 A t)). Qed.
Lemma lem1114146 {A : Type'} (t : list A) (h : A) : term255 A t h.
Proof. exact (@lem1114145 A t h). Qed.
Lemma lem1114147 {A : Type'} (h : A) (t : list A) : (term255 A t h) = (term68 A h t).
Proof. exact (eq_refl (term255 A t h)). Qed.
Lemma lem1114148 {A : Type'} (h : A) (t : list A) : term68 A h t.
Proof. exact (EQ_MP (@lem1114147 A h t) (@lem1114146 A t h)). Qed.
Lemma lem1114150 {A : Type'} (h : A) (t : list A) : term68 A h t.
Proof. exact (@lem1113627 A h t (@lem1114148 A h t)). Qed.
Lemma lem1114151 {A : Type'} (h : A) (t : list A) (h1 : term69 A h t) : False.
Proof. exact (@lem1114150 A h t (@lem1113611 A h t h1)). Qed.
Lemma lem1114152 {A : Type'} (h : A) (t : list A) (h1 : term69 A h t) : (term69 A h t) = False.
Proof. exact (prop_ext (fun h2 : term69 A h t => @lem1114151 A h t h1) (fun h2 : False => @lem1113611 A h t h1)). Qed.
Lemma lem1114153 {A : Type'} (h : A) (t : list A) (h1 : term69 A h t) : False.
Proof. exact (EQ_MP (@lem1114152 A h t h1) (@lem1113611 A h t h1)). Qed.
Lemma lem1114154 {A : Type'} (h : A) (t : list A) : term68 A h t.
Proof. exact (fun h0 : term69 A h t => @lem1114153 A h t h0). Qed.
Lemma lem1114155 {A : Type'} (h : A) (t : list A) : term65 A h t.
Proof. exact (EQ_MP (@lem1113610 A h t) (@lem1114154 A h t)). Qed.
Lemma lem1114156 {A : Type'} (h : A) (t : list A) : term27 A h t.
Proof. exact (EQ_MP (@lem1113606 A h t) (@lem1114155 A h t)). Qed.
Lemma lem1114157 {A : Type'} (h : A) (t : list A) : term29 A h t.
Proof. exact (fun h0 : term23 A t => @lem1114156 A h t). Qed.
Lemma lem1114162 {A : Type'} (h : A) : term33 A h.
Proof. exact (fun t : list A => @lem1114157 A h t). Qed.
Lemma lem1114167 {A : Type'} : term37 A.
Proof. exact (fun h : A => @lem1114162 A h). Qed.
Lemma lem1114168 {A : Type'} : term39 A.
Proof. exact (conj (@lem1113547 A) (@lem1114167 A)). Qed.
Lemma lem1114169 {A : Type'} : term44 A.
Proof. exact (@lem1113504 A (@lem1114168 A)). Qed.
