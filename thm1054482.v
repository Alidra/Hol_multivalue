Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1054482_term_abbrevs.
Require Import INJ_INVERSE2_spec.
Require Import NUMSUM_INJ_spec.
Require Import SKOLEM_THM_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1054432 {A B C : Type'} (P : type1412 A B C) : term0 A B C P.
Proof. exact (@lem1046586 A B C P). Qed.
Lemma lem1054433 {A B C : Type'} (P : type1412 A B C) : (term0 A B C P) = (term1 A B C P).
Proof. exact (eq_refl (term0 A B C P)). Qed.
Lemma lem1054436 {A B C : Type'} (P : type1412 A B C) : term1 A B C P.
Proof. exact (EQ_MP (@lem1054433 A B C P) (@lem1054432 A B C P)). Qed.
Lemma lem1054437 (P : type1545) : term2 P.
Proof. exact (@lem1054436 Prop nat nat P). Qed.
Lemma lem1054438 : term3.
Proof. exact (@lem1054437 NUMSUM). Qed.
Lemma lem1054439 : term4.
Proof. exact (@lem1054438 (@lem1054431)). Qed.
Lemma lem1054440 : term5.
Proof. exact (fun _17372 : type1670 => @lem1054439). Qed.
Lemma lem1054441 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1054442 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem1054445 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem1054442 A B P) (@lem1054441 A B P)). Qed.
Lemma lem1054446 (P : type1257) : (term9 P) = (term10 P).
Proof. exact (@lem1054445 type1670 (nat -> Prop) P). Qed.
Lemma lem1054447 : term11 = term12.
Proof. exact (@lem1054446 term13). Qed.
Lemma lem1054448 (_17372 : type1670) : (term14 _17372) = term15.
Proof. exact (eq_refl (term14 _17372)). Qed.
Lemma lem1054449 (X : nat -> Prop) : X = X.
Proof. exact (eq_refl X). Qed.
Lemma lem1054450 (_17372 : type1670) (X : nat -> Prop) : (term16 _17372 X) = (term17 X).
Proof. exact (MK_COMB (@lem1054448 _17372) (@lem1054449 X)). Qed.
Lemma lem1054451 (X : nat -> Prop) : (term17 X) = (term18 X).
Proof. exact (eq_refl (term17 X)). Qed.
Lemma lem1054452 (_17372 : type1670) (X : nat -> Prop) : (term16 _17372 X) = (term18 X).
Proof. exact (TRANS (@lem1054450 _17372 X) (@lem1054451 X)). Qed.
Lemma lem1054453 (_17372 : type1670) : (term19 _17372) = term15.
Proof. exact (fun_ext (fun X : nat -> Prop => @lem1054452 _17372 X)). Qed.
Lemma lem1054454 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem1054455 (_17372 : type1670) : (term20 _17372) = term4.
Proof. exact (MK_COMB (@lem1054454) (@lem1054453 _17372)). Qed.
Lemma lem1054456 : term21 = term22.
Proof. exact (fun_ext (fun _17372 : type1670 => @lem1054455 _17372)). Qed.
Lemma lem1054457 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1054458 : term11 = term5.
Proof. exact (MK_COMB (@lem1054457) (@lem1054456)). Qed.
Lemma lem1054459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054460 : term23 = term24.
Proof. exact (MK_COMB (@lem1054459) (@lem1054458)). Qed.
Lemma lem1054461 (_17372 : type1670) : (term14 _17372) = term15.
Proof. exact (eq_refl (term14 _17372)). Qed.
Lemma lem1054462 (X : type1260) (_17372 : type1670) : (X _17372) = (X _17372).
Proof. exact (eq_refl (X _17372)). Qed.
Lemma lem1054463 (X : type1260) (_17372 : type1670) : (term25 X _17372) = (term26 X _17372).
Proof. exact (MK_COMB (@lem1054461 _17372) (@lem1054462 X _17372)). Qed.
Lemma lem1054464 (X : type1260) (_17372 : type1670) : (term26 X _17372) = (term27 X _17372).
Proof. exact (eq_refl (term26 X _17372)). Qed.
Lemma lem1054465 (X : type1260) (_17372 : type1670) : (term25 X _17372) = (term27 X _17372).
Proof. exact (TRANS (@lem1054463 X _17372) (@lem1054464 X _17372)). Qed.
Lemma lem1054466 (X : type1260) : (term28 X) = (term29 X).
Proof. exact (fun_ext (fun _17372 : type1670 => @lem1054465 X _17372)). Qed.
Lemma lem1054467 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1054468 (X : type1260) : (term30 X) = (term31 X).
Proof. exact (MK_COMB (@lem1054467) (@lem1054466 X)). Qed.
Lemma lem1054469 : term32 = term33.
Proof. exact (fun_ext (fun X : type1260 => @lem1054468 X)). Qed.
Lemma lem1054470 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop))). Qed.
Lemma lem1054471 : term12 = term34.
Proof. exact (MK_COMB (@lem1054470) (@lem1054469)). Qed.
Lemma lem1054472 : (term11 = term12) = (term5 = term34).
Proof. exact (MK_COMB (@lem1054460) (@lem1054471)). Qed.
Lemma lem1054473 : term5 = term34.
Proof. exact (EQ_MP (@lem1054472) (@lem1054447)). Qed.
Lemma lem1054474 : term34.
Proof. exact (EQ_MP (@lem1054473) (@lem1054440)). Qed.
Lemma lem1054476 {A : Type'} : (@ex A) = (term35 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1054477 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop)) = term36.
Proof. exact (@lem1054476 type1260). Qed.
Lemma lem1054478 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1054479 : term34 = term37.
Proof. exact (MK_COMB (@lem1054477) (@lem1054478)). Qed.
Lemma lem1054480 : term37 = term38.
Proof. exact (eq_refl term37). Qed.
Lemma lem1054481 : term34 = term38.
Proof. exact (TRANS (@lem1054479) (@lem1054480)). Qed.
Lemma lem1054482 : term38.
Proof. exact (EQ_MP (@lem1054481) (@lem1054474)). Qed.
