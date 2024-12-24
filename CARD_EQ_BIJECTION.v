Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_BIJECTION_term_abbrevs.
Require Import CARD_LE_INJ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import LE_REFL_spec.
Require Import MONO_EXISTS_spec.
Require Import MONO_FORALL_spec.
Require Import SUBSET_spec.
Require Import SURJECTIVE_IFF_INJECTIVE_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem5056433 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5056434 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5056435 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5056434 t1) (@lem5056433 t1)). Qed.
Lemma lem5056436 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5056435 t1 t2). Qed.
Lemma lem5056437 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5056438 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5056437 t1 t2) (@lem5056436 t1 t2)). Qed.
Lemma lem5056439 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5056438 t1 t2 t3). Qed.
Lemma lem5056440 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5056441 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5056440 t1 t2 t3) (@lem5056439 t1 t2 t3)). Qed.
Lemma lem5056442 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5056441 t1 t2 t3)). Qed.
Lemma lem5056443 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056444 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term8 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056445 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5056443 A P Q h2 (@lem5056444 A P Q h1)). Qed.
Lemma lem5056446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term10 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5056445 A P Q h1 h0). Qed.
Lemma lem5056447 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056448 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5056446 A P Q h1 (@lem5056447 A P Q h2)). Qed.
Lemma lem5056449 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term8 A P Q => @lem5056448 A P Q h0 h1). Qed.
Lemma lem5056450 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5056449 A P Q h0). Qed.
Lemma lem5056452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term12 A P Q) : term12 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056453 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term8 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056454 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term12 A P Q) : term13 A P Q.
Proof. exact (@lem5056452 A P Q h2 (@lem5056453 A P Q h1)). Qed.
Lemma lem5056455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term14 A P Q.
Proof. exact (fun h0 : term12 A P Q => @lem5056454 A P Q h1 h0). Qed.
Lemma lem5056456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term12 A P Q) : term12 A P Q.
Proof. exact (h1). Qed.
Lemma lem5056457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term12 A P Q) : term13 A P Q.
Proof. exact (@lem5056455 A P Q h1 (@lem5056456 A P Q h2)). Qed.
Lemma lem5056458 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term12 A P Q) : term12 A P Q.
Proof. exact (fun h0 : term8 A P Q => @lem5056457 A P Q h0 h1). Qed.
Lemma lem5056459 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term15 A P Q.
Proof. exact (fun h0 : term12 A P Q => @lem5056458 A P Q h0). Qed.
Lemma lem5056462 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term12 A P Q.
Proof. exact (@lem5056459 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5056463 {A : Type'} (P : type686 A) (Q : type686 A) : term16 A P Q.
Proof. exact (@lem5056462 (A -> Prop) P Q). Qed.
Lemma lem5056464 {A B : Type'} : term17 A B.
Proof. exact (@lem5056463 A (term18 A B) (term19 A B)). Qed.
Lemma lem5056465 {A B : Type'} (s : A -> Prop) : (term20 A B s) = (term21 A B s).
Proof. exact (eq_refl (term20 A B s)). Qed.
Lemma lem5056466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056467 {A B : Type'} (s : A -> Prop) : (term22 A B s) = (term23 A B s).
Proof. exact (MK_COMB (@lem5056466) (@lem5056465 A B s)). Qed.
Lemma lem5056468 {A B : Type'} (s : A -> Prop) : (term24 A B s) = (term25 A B s).
Proof. exact (eq_refl (term24 A B s)). Qed.
Lemma lem5056469 {A B : Type'} (s : A -> Prop) : (term26 A B s) = (term27 A B s).
Proof. exact (MK_COMB (@lem5056467 A B s) (@lem5056468 A B s)). Qed.
Lemma lem5056470 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5056469 A B s)). Qed.
Lemma lem5056471 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5056472 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem5056471 A) (@lem5056470 A B)). Qed.
Lemma lem5056473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056474 {A B : Type'} : (term32 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem5056473) (@lem5056472 A B)). Qed.
Lemma lem5056475 {A B : Type'} (s : A -> Prop) : (term20 A B s) = (term21 A B s).
Proof. exact (eq_refl (term20 A B s)). Qed.
Lemma lem5056476 {A B : Type'} : (term34 A B) = (term18 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5056475 A B s)). Qed.
Lemma lem5056477 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5056478 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem5056477 A) (@lem5056476 A B)). Qed.
Lemma lem5056479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056480 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem5056479) (@lem5056478 A B)). Qed.
Lemma lem5056481 {A B : Type'} (s : A -> Prop) : (term24 A B s) = (term25 A B s).
Proof. exact (eq_refl (term24 A B s)). Qed.
Lemma lem5056482 {A B : Type'} : (term39 A B) = (term19 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5056481 A B s)). Qed.
Lemma lem5056483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5056484 {A B : Type'} : (term40 A B) = (term41 A B).
Proof. exact (MK_COMB (@lem5056483 A) (@lem5056482 A B)). Qed.
Lemma lem5056485 {A B : Type'} : (term42 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem5056480 A B) (@lem5056484 A B)). Qed.
Lemma lem5056486 {A B : Type'} : (term17 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem5056474 A B) (@lem5056485 A B)). Qed.
Lemma lem5056487 {A B : Type'} : term44 A B.
Proof. exact (EQ_MP (@lem5056486 A B) (@lem5056464 A B)). Qed.
Lemma lem5056489 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term12 A P Q.
Proof. exact (@lem5056459 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5056490 {B : Type'} (P : type686 B) (Q : type686 B) : term16 B P Q.
Proof. exact (@lem5056489 (B -> Prop) P Q). Qed.
Lemma lem5056491 {A B : Type'} (s : A -> Prop) : term45 A B s.
Proof. exact (@lem5056490 B (term46 A B s) (term47 A B s)). Qed.
Lemma lem5056492 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term48 A B s t) = (term49 A B t s).
Proof. exact (eq_refl (term48 A B s t)). Qed.
Lemma lem5056493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056494 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term50 A B s t) = (term51 A B t s).
Proof. exact (MK_COMB (@lem5056493) (@lem5056492 A B t s)). Qed.
Lemma lem5056495 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term52 A B s t) = (term53 A B t s).
Proof. exact (eq_refl (term52 A B s t)). Qed.
Lemma lem5056496 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term54 A B s t) = (term55 A B t s).
Proof. exact (MK_COMB (@lem5056494 A B t s) (@lem5056495 A B t s)). Qed.
Lemma lem5056497 {A B : Type'} (s : A -> Prop) : (term56 A B s) = (term57 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5056496 A B t s)). Qed.
Lemma lem5056498 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5056499 {A B : Type'} (s : A -> Prop) : (term58 A B s) = (term59 A B s).
Proof. exact (MK_COMB (@lem5056498 B) (@lem5056497 A B s)). Qed.
Lemma lem5056500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056501 {A B : Type'} (s : A -> Prop) : (term60 A B s) = (term61 A B s).
Proof. exact (MK_COMB (@lem5056500) (@lem5056499 A B s)). Qed.
Lemma lem5056502 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term48 A B s t) = (term49 A B t s).
Proof. exact (eq_refl (term48 A B s t)). Qed.
Lemma lem5056503 {A B : Type'} (s : A -> Prop) : (term62 A B s) = (term46 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5056502 A B t s)). Qed.
Lemma lem5056504 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5056505 {A B : Type'} (s : A -> Prop) : (term63 A B s) = (term21 A B s).
Proof. exact (MK_COMB (@lem5056504 B) (@lem5056503 A B s)). Qed.
Lemma lem5056506 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056507 {A B : Type'} (s : A -> Prop) : (term64 A B s) = (term23 A B s).
Proof. exact (MK_COMB (@lem5056506) (@lem5056505 A B s)). Qed.
Lemma lem5056508 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term52 A B s t) = (term53 A B t s).
Proof. exact (eq_refl (term52 A B s t)). Qed.
Lemma lem5056509 {A B : Type'} (s : A -> Prop) : (term65 A B s) = (term47 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5056508 A B t s)). Qed.
Lemma lem5056510 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5056511 {A B : Type'} (s : A -> Prop) : (term66 A B s) = (term25 A B s).
Proof. exact (MK_COMB (@lem5056510 B) (@lem5056509 A B s)). Qed.
Lemma lem5056512 {A B : Type'} (s : A -> Prop) : (term67 A B s) = (term27 A B s).
Proof. exact (MK_COMB (@lem5056507 A B s) (@lem5056511 A B s)). Qed.
Lemma lem5056513 {A B : Type'} (s : A -> Prop) : (term45 A B s) = (term68 A B s).
Proof. exact (MK_COMB (@lem5056501 A B s) (@lem5056512 A B s)). Qed.
Lemma lem5056514 {A B : Type'} (s : A -> Prop) : term68 A B s.
Proof. exact (EQ_MP (@lem5056513 A B s) (@lem5056491 A B s)). Qed.
Lemma lem5056517 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term49 A B t s) : term49 A B t s.
Proof. exact (h1). Qed.
Lemma lem5056518 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term69 A B s t) : term69 A B s t.
Proof. exact (h1). Qed.
Lemma lem5056519 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term70 A B s t) : term70 A B s t.
Proof. exact (h1). Qed.
Lemma lem5056520 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5056521 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5056522 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5056523 (n : nat) : term71 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem5056524 (n : nat) : (term71 n) = (Peano.le n n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem5056525 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem5056524 n) (@lem5056523 n)). Qed.
Lemma lem5056526 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem5056528 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5056530 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem5056539 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5056528 A s) (@lem5056520 A s h1)). Qed.
Lemma lem5056540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056541 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term72 A s) = (and True).
Proof. exact (MK_COMB (@lem5056540) (@lem5056539 A s h1)). Qed.
Lemma lem5056545 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5056530 B t) (@lem5056522 B t h1)). Qed.
Lemma lem5056546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5056547 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term72 B t) = (and True).
Proof. exact (MK_COMB (@lem5056546) (@lem5056545 B t h1)). Qed.
Lemma lem5056551 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5056552 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem5056553 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term73 A s) = (term73 B t).
Proof. exact (MK_COMB (@lem5056552) (@lem5056551 A B s t h1)). Qed.
Lemma lem5056554 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem5056555 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term74 A B s t) = (term75 B t).
Proof. exact (MK_COMB (@lem5056553 A B s t h1) (@lem5056554 B t)). Qed.
Lemma lem5056557 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem5056526 n) (@lem5056525 n)). Qed.
Lemma lem5056558 {B : Type'} (t : B -> Prop) : (term75 B t) = True.
Proof. exact (@lem5056557 (@CARD B t)). Qed.
Lemma lem5056559 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term74 A B s t) = True.
Proof. exact (TRANS (@lem5056555 A B s t h1) (@lem5056558 B t)). Qed.
Lemma lem5056560 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : (@CARD A s) = (@CARD B t)) : (term76 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5056547 B t h1) (@lem5056559 A B s t h2)). Qed.
Lemma lem5056562 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056563 : (True /\ True) = True.
Proof. exact (@lem5056562 True). Qed.
Lemma lem5056564 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : (@CARD A s) = (@CARD B t)) : (term76 A B s t) = True.
Proof. exact (TRANS (@lem5056560 A B s t h1 h2) (@lem5056563)). Qed.
Lemma lem5056565 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term77 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5056541 A s h1) (@lem5056564 A B s t h2 h3)). Qed.
Lemma lem5056567 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5056568 : (True /\ True) = True.
Proof. exact (@lem5056567 True). Qed.
Lemma lem5056569 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term77 A B s t) = True.
Proof. exact (TRANS (@lem5056565 A B s t h1 h2 h3) (@lem5056568)). Qed.
Lemma lem5056570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056571 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term78 A B s t) = (imp True).
Proof. exact (MK_COMB (@lem5056570) (@lem5056569 A B s t h1 h2 h3)). Qed.
Lemma lem5056596 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term79 A B t s) = (term79 A B t s).
Proof. exact (eq_refl (term79 A B t s)). Qed.
Lemma lem5056597 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term49 A B t s) = (term80 A B t s).
Proof. exact (MK_COMB (@lem5056571 A B s t h1 h2 h3) (@lem5056596 A B t s)). Qed.
Lemma lem5056599 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5056600 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term80 A B t s) = (term79 A B t s).
Proof. exact (@lem5056599 (term79 A B t s)). Qed.
Lemma lem5056625 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term49 A B t s) = (term79 A B t s).
Proof. exact (TRANS (@lem5056597 A B s t h1 h2 h3) (@lem5056600 A B t s)). Qed.
Lemma lem5056626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056627 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term51 A B t s) = (term81 A B t s).
Proof. exact (MK_COMB (@lem5056626) (@lem5056625 A B s t h1 h2 h3)). Qed.
Lemma lem5056674 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term82 A B t s) = (term82 A B t s).
Proof. exact (eq_refl (term82 A B t s)). Qed.
Lemma lem5056675 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term83 A B t s) = (term84 A B t s).
Proof. exact (MK_COMB (@lem5056627 A B s t h1 h2 h3) (@lem5056674 A B t s)). Qed.
Lemma lem5056678 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term84 A B t s) = (term83 A B t s).
Proof. exact (SYM (@lem5056675 A B s t h1 h2 h3)). Qed.
Lemma lem5056680 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem5056450 A P Q (@lem7401 A P Q)). Qed.
Lemma lem5056681 {A B : Type'} (P : type572 A B) (Q : type572 A B) : term85 A B P Q.
Proof. exact (@lem5056680 (A -> B) P Q). Qed.
Lemma lem5056682 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term86 A B t s.
Proof. exact (@lem5056681 A B (term87 A B t s) (term88 A B t s)). Qed.
Lemma lem5056683 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term89 A B t s f) = (term90 A B t s f).
Proof. exact (eq_refl (term89 A B t s f)). Qed.
Lemma lem5056684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056685 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term91 A B t s f) = (term92 A B t s f).
Proof. exact (MK_COMB (@lem5056684) (@lem5056683 A B t s f)). Qed.
Lemma lem5056686 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term93 A B t s f) = (term94 A B t s f).
Proof. exact (eq_refl (term93 A B t s f)). Qed.
Lemma lem5056687 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term95 A B t s f) = (term96 A B t s f).
Proof. exact (MK_COMB (@lem5056685 A B t s f) (@lem5056686 A B t s f)). Qed.
Lemma lem5056688 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term97 A B t s) = (term98 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5056687 A B t s f)). Qed.
Lemma lem5056689 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5056690 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term99 A B t s) = (term100 A B t s).
Proof. exact (MK_COMB (@lem5056689 A B) (@lem5056688 A B t s)). Qed.
Lemma lem5056691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056692 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term101 A B t s) = (term102 A B t s).
Proof. exact (MK_COMB (@lem5056691) (@lem5056690 A B t s)). Qed.
Lemma lem5056693 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term89 A B t s f) = (term90 A B t s f).
Proof. exact (eq_refl (term89 A B t s f)). Qed.
Lemma lem5056694 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term103 A B t s) = (term87 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5056693 A B t s f)). Qed.
Lemma lem5056695 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5056696 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term104 A B t s) = (term79 A B t s).
Proof. exact (MK_COMB (@lem5056695 A B) (@lem5056694 A B t s)). Qed.
Lemma lem5056697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5056698 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term105 A B t s) = (term81 A B t s).
Proof. exact (MK_COMB (@lem5056697) (@lem5056696 A B t s)). Qed.
Lemma lem5056699 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term93 A B t s f) = (term94 A B t s f).
Proof. exact (eq_refl (term93 A B t s f)). Qed.
Lemma lem5056700 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term106 A B t s) = (term88 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5056699 A B t s f)). Qed.
Lemma lem5056701 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5056702 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term107 A B t s) = (term82 A B t s).
Proof. exact (MK_COMB (@lem5056701 A B) (@lem5056700 A B t s)). Qed.
Lemma lem5056703 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term108 A B t s) = (term84 A B t s).
Proof. exact (MK_COMB (@lem5056698 A B t s) (@lem5056702 A B t s)). Qed.
Lemma lem5056704 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term86 A B t s) = (term109 A B t s).
Proof. exact (MK_COMB (@lem5056692 A B t s) (@lem5056703 A B t s)). Qed.
Lemma lem5056705 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term109 A B t s.
Proof. exact (EQ_MP (@lem5056704 A B t s) (@lem5056682 A B t s)). Qed.
Lemma lem5056706 {A B : Type'} (s : A -> Prop) : term110 A B s.
Proof. exact (@lem4944739 A B s). Qed.
Lemma lem5056707 {A B : Type'} (s : A -> Prop) : (term110 A B s) = (term111 A B s).
Proof. exact (eq_refl (term110 A B s)). Qed.
Lemma lem5056708 {A B : Type'} (s : A -> Prop) : term111 A B s.
Proof. exact (EQ_MP (@lem5056707 A B s) (@lem5056706 A B s)). Qed.
Lemma lem5056709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term112 A B s t.
Proof. exact (@lem5056708 A B s t). Qed.
Lemma lem5056710 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term112 A B s t) = (term113 A B t s).
Proof. exact (eq_refl (term112 A B s t)). Qed.
Lemma lem5056711 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term113 A B t s.
Proof. exact (EQ_MP (@lem5056710 A B t s) (@lem5056709 A B s t)). Qed.
Lemma lem5056712 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term114 A B t s f.
Proof. exact (@lem5056711 A B t s f). Qed.
Lemma lem5056713 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term114 A B t s f) = (term115 A B t s f).
Proof. exact (eq_refl (term114 A B t s f)). Qed.
Lemma lem5056714 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term115 A B t s f.
Proof. exact (EQ_MP (@lem5056713 A B t s f) (@lem5056712 A B t s f)). Qed.
Lemma lem5056715 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term116 A B f s t) : term116 A B f s t.
Proof. exact (h1). Qed.
Lemma lem5056716 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term116 A B f s t) : (term117 A B t s f) = (term118 A B s f).
Proof. exact (@lem5056714 A B t s f (@lem5056715 A B f s t h1)). Qed.
Lemma lem5056722 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5056724 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem5056733 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term119 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5056734 (p : Prop) (q : Prop) (p' : Prop) : term120 p q p'.
Proof. exact (fun q' : Prop => @lem5056733 p q p' q'). Qed.
Lemma lem5056735 (p : Prop) (q : Prop) : term121 p q.
Proof. exact (fun p' : Prop => @lem5056734 p q p'). Qed.
Lemma lem5056736 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term122 A B t s f.
Proof. exact (@lem5056735 (term90 A B t s f) (term94 A B t s f)). Qed.
Lemma lem5056737 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term123 A B t s f p'.
Proof. exact (@lem5056736 A B t s f p'). Qed.
Lemma lem5056738 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term123 A B t s f p') = (term124 A B t s f p').
Proof. exact (eq_refl (term123 A B t s f p')). Qed.
Lemma lem5056739 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term124 A B t s f p'.
Proof. exact (EQ_MP (@lem5056738 A B t s f p') (@lem5056737 A B t s f p')). Qed.
Lemma lem5056740 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term125 A B t s f p' q'.
Proof. exact (@lem5056739 A B t s f p' q'). Qed.
Lemma lem5056741 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term125 A B t s f p' q') = (term126 A B t s f p' q').
Proof. exact (eq_refl (term125 A B t s f p' q')). Qed.
Lemma lem5056742 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term126 A B t s f p' q'.
Proof. exact (EQ_MP (@lem5056741 A B t s f p' q') (@lem5056740 A B t s f p' q')). Qed.
Lemma lem5056798 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term90 A B t s f) = (term90 A B t s f).
Proof. exact (eq_refl (term90 A B t s f)). Qed.
Lemma lem5056799 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (q' : Prop) : term127 A B t s f q'.
Proof. exact (@lem5056742 A B t s f (term90 A B t s f) q'). Qed.
Lemma lem5056800 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (q' : Prop) : term128 A B t s f q'.
Proof. exact (@lem5056799 A B t s f q' (@lem5056798 A B t s f)). Qed.
Lemma lem5056801 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term90 A B t s f) : term90 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5056816 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term90 A B t s f) : term129 A B f s t.
Proof. exact (proj1 (@lem5056801 A B t s f h1)). Qed.
Lemma lem5056817 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term129 A B f s t) = ((term129 A B f s t) = True).
Proof. exact (@lem7 (term129 A B f s t)). Qed.
Lemma lem5056991 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term115 A B t s f.
Proof. exact (fun h0 : term116 A B f s t => @lem5056716 A B f s t h0). Qed.
Lemma lem5056992 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term115 A B t s f.
Proof. exact (@lem5056991 A B t s f). Qed.
Lemma lem5057008 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5056722 A s) (@lem5056520 A s h1)). Qed.
Lemma lem5057013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5057014 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term72 A s) = (and True).
Proof. exact (MK_COMB (@lem5057013) (@lem5057008 A s h1)). Qed.
Lemma lem5057042 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5056724 B t) (@lem5056522 B t h1)). Qed.
Lemma lem5057047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5057048 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term72 B t) = (and True).
Proof. exact (MK_COMB (@lem5057047) (@lem5057042 B t h1)). Qed.
Lemma lem5057090 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5057103 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5057104 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term130 A s) = (term130 B t).
Proof. exact (MK_COMB (@lem5057103) (@lem5057090 A B s t h1)). Qed.
Lemma lem5057137 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem5057138 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = ((@CARD B t) = (@CARD B t)).
Proof. exact (MK_COMB (@lem5057104 A B s t h1) (@lem5057137 B t)). Qed.
Lemma lem5057140 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5057141 (x : nat) : (x = x) = True.
Proof. exact (@lem5057140 nat x). Qed.
Lemma lem5057142 {B : Type'} (t : B -> Prop) : ((@CARD B t) = (@CARD B t)) = True.
Proof. exact (@lem5057141 (@CARD B t)). Qed.
Lemma lem5057147 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = True.
Proof. exact (TRANS (@lem5057138 A B s t h1) (@lem5057142 B t)). Qed.
Lemma lem5057148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5057149 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term131 A B s t) = (and True).
Proof. exact (MK_COMB (@lem5057148) (@lem5057147 A B s t h1)). Qed.
Lemma lem5057163 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term90 A B t s f) : (term129 A B f s t) = True.
Proof. exact (EQ_MP (@lem5056817 A B f s t) (@lem5056816 A B t s f h1)). Qed.
Lemma lem5057168 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term90 A B t s f) (h2 : (@CARD A s) = (@CARD B t)) : (term132 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5057149 A B s t h2) (@lem5057163 A B t s f h1)). Qed.
Lemma lem5057170 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5057171 : (True /\ True) = True.
Proof. exact (@lem5057170 True). Qed.
Lemma lem5057176 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term90 A B t s f) (h2 : (@CARD A s) = (@CARD B t)) : (term132 A B f s t) = True.
Proof. exact (TRANS (@lem5057168 A B f s t h1 h2) (@lem5057171)). Qed.
Lemma lem5057177 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term90 A B t s f) (h3 : (@CARD A s) = (@CARD B t)) : (term133 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5057048 B t h1) (@lem5057176 A B f s t h2 h3)). Qed.
Lemma lem5057179 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5057180 : (True /\ True) = True.
Proof. exact (@lem5057179 True). Qed.
Lemma lem5057185 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term90 A B t s f) (h3 : (@CARD A s) = (@CARD B t)) : (term133 A B f s t) = True.
Proof. exact (TRANS (@lem5057177 A B f s t h1 h2 h3) (@lem5057180)). Qed.
Lemma lem5057186 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term116 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5057014 A s h1) (@lem5057185 A B f s t h2 h3 h4)). Qed.
Lemma lem5057188 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5057189 : (True /\ True) = True.
Proof. exact (@lem5057188 True). Qed.
Lemma lem5057194 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term116 A B f s t) = True.
Proof. exact (TRANS (@lem5057186 A B f s t h1 h2 h3 h4) (@lem5057189)). Qed.
Lemma lem5057195 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : True = (term116 A B f s t).
Proof. exact (SYM (@lem5057194 A B f s t h1 h2 h3 h4)). Qed.
Lemma lem5057196 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : term116 A B f s t.
Proof. exact (EQ_MP (@lem5057195 A B f s t h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem5057197 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term117 A B t s f) = (term118 A B s f).
Proof. exact (@lem5056992 A B t s f (@lem5057196 A B f s t h1 h2 h3 h4)). Qed.
Lemma lem5057521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5057522 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term134 A B t s f) = (term135 A B s f).
Proof. exact (MK_COMB (@lem5057521) (@lem5057197 A B f s t h1 h2 h3 h4)). Qed.
Lemma lem5058177 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (eq_refl (term118 A B s f)). Qed.
Lemma lem5058178 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term136 A B t s f) = (term137 A B s f).
Proof. exact (MK_COMB (@lem5057522 A B f s t h1 h2 h3 h4) (@lem5058177 A B s f)). Qed.
Lemma lem5058180 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem5058181 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term137 A B s f) = (term118 A B s f).
Proof. exact (@lem5058180 (term118 A B s f)). Qed.
Lemma lem5058505 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term136 A B t s f) = (term118 A B s f).
Proof. exact (TRANS (@lem5058178 A B f s t h1 h2 h3 h4) (@lem5058181 A B s f)). Qed.
Lemma lem5058506 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term138 A B s f t) = (term138 A B s f t).
Proof. exact (eq_refl (term138 A B s f t)). Qed.
Lemma lem5058507 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term90 A B t s f) (h4 : (@CARD A s) = (@CARD B t)) : (term94 A B t s f) = (term139 A B t s f).
Proof. exact (MK_COMB (@lem5058506 A B s f t) (@lem5058505 A B f s t h1 h2 h3 h4)). Qed.
Lemma lem5058988 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term140 A B t s f.
Proof. exact (fun h0 : term90 A B t s f => @lem5058507 A B f s t h1 h2 h0 h3). Qed.
Lemma lem5058989 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term141 A B t s f.
Proof. exact (@lem5056800 A B t s f (term139 A B t s f)). Qed.
Lemma lem5058990 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term96 A B t s f) = (term142 A B t s f).
Proof. exact (@lem5058989 A B t s f (@lem5058988 A B f s t h1 h2 h3)). Qed.
Lemma lem5059701 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term98 A B t s) = (term143 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5058990 A B f s t h1 h2 h3)). Qed.
Lemma lem5060412 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5060413 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term100 A B t s) = (term144 A B t s).
Proof. exact (MK_COMB (@lem5060412 A B) (@lem5059701 A B s t h1 h2 h3)). Qed.
Lemma lem5061128 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : (term144 A B t s) = (term100 A B t s).
Proof. exact (SYM (@lem5060413 A B s t h1 h2 h3)). Qed.
Lemma lem5061130 (p : Prop) : p = (term145 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5061131 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term144 A B t s) = (term146 A B t s).
Proof. exact (@lem5061130 (term144 A B t s)). Qed.
Lemma lem5061132 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term146 A B t s) = (term144 A B t s).
Proof. exact (SYM (@lem5061131 A B t s)). Qed.
Lemma lem5061133 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term147 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061134 {B : Type'} : term148 B.
Proof. exact (@lem3194148 B). Qed.
Lemma lem5061135 {A : Type'} : term148 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem5061137 {A : Type'} : term149 A.
Proof. exact (@lem3206070 A A). Qed.
Lemma lem5061138 {A B : Type'} : term150 A B.
Proof. exact (@lem3206070 A B). Qed.
Lemma lem5061143 {B : Type'} : term149 B.
Proof. exact (@lem3206070 B B). Qed.
Lemma lem5061146 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s) : term151 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061147 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term152 A B t s.
Proof. exact (fun h0 : term151 A B t s => @lem5061146 A B t s h0). Qed.
Lemma lem5061148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term152 A B t s) : term152 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061149 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s) : term151 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061150 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s) (h2 : term152 A B t s) : term151 A B t s.
Proof. exact (@lem5061148 A B t s h2 (@lem5061149 A B t s h1)). Qed.
Lemma lem5061151 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s) : term153 A B t s.
Proof. exact (fun h0 : term152 A B t s => @lem5061150 A B t s h1 h0). Qed.
Lemma lem5061152 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term152 A B t s) : term152 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061153 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s) (h2 : term152 A B t s) : term151 A B t s.
Proof. exact (@lem5061151 A B t s h1 (@lem5061152 A B t s h2)). Qed.
Lemma lem5061154 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term152 A B t s) : term152 A B t s.
Proof. exact (fun h0 : term151 A B t s => @lem5061153 A B t s h0 h1). Qed.
Lemma lem5061155 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term154 A B t s.
Proof. exact (fun h0 : term152 A B t s => @lem5061154 A B t s h0). Qed.
Lemma lem5061158 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term152 A B t s.
Proof. exact (@lem5061155 A B t s (@lem5061147 A B t s)). Qed.
Lemma lem5061159 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term152 A B t s.
Proof. exact (@lem5061158 A B t s). Qed.
Lemma lem5061423 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5061424 {B : Type'} : (term155 B) = (term156 B).
Proof. exact (@lem5061423 (term148 B)). Qed.
Lemma lem5061439 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (eq_refl (term157 A)). Qed.
Lemma lem5061440 {A B : Type'} : (term158 A B) = (term159 A B).
Proof. exact (MK_COMB (@lem5061439 A) (@lem5061424 B)). Qed.
Lemma lem5061443 {B : Type'} : (term160 B) = (term160 B).
Proof. exact (eq_refl (term160 B)). Qed.
Lemma lem5061444 {A B : Type'} : (term161 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem5061443 B) (@lem5061440 A B)). Qed.
Lemma lem5061447 {A B : Type'} : (term163 A B) = (term163 A B).
Proof. exact (eq_refl (term163 A B)). Qed.
Lemma lem5061448 {A B : Type'} : (term164 A B) = (term165 A B).
Proof. exact (MK_COMB (@lem5061447 A B) (@lem5061444 A B)). Qed.
Lemma lem5061451 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem5061452 {A B : Type'} : (term166 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem5061451 A) (@lem5061448 A B)). Qed.
Lemma lem5061455 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term168 A B t s) = (term168 A B t s).
Proof. exact (eq_refl (term168 A B t s)). Qed.
Lemma lem5061456 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term151 A B t s) = (term169 A B t s).
Proof. exact (MK_COMB (@lem5061455 A B t s) (@lem5061452 A B)). Qed.
Lemma lem5061459 {A B : Type'} (s : A -> Prop) : (term170 A B s) = (term171 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5061456 A B t s)). Qed.
Lemma lem5061460 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5061461 {A B : Type'} (s : A -> Prop) : (term172 A B s) = (term173 A B s).
Proof. exact (MK_COMB (@lem5061460 B) (@lem5061459 A B s)). Qed.
Lemma lem5061466 {A B : Type'} : (term174 A B) = (term175 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5061461 A B s)). Qed.
Lemma lem5061467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061476 {A B : Type'} : (term176 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem5061467 A) (@lem5061466 A B)). Qed.
Lemma lem5061481 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term178 B s x t) = (term178 B s x t).
Proof. exact (eq_refl (term178 B s x t)). Qed.
Lemma lem5061482 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term179 B s t) = (term179 B s t).
Proof. exact (fun_ext (fun x : B => @lem5061481 B s x t)). Qed.
Lemma lem5061483 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5061484 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term180 B s t) = (term180 B s t).
Proof. exact (MK_COMB (@lem5061483 B) (@lem5061482 B s t)). Qed.
Lemma lem5061487 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term181 B s t) = (term181 B s t).
Proof. exact (eq_refl (term181 B s t)). Qed.
Lemma lem5061488 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term180 B s t)) = ((@SUBSET B s t) = (term180 B s t)).
Proof. exact (MK_COMB (@lem5061487 B s t) (@lem5061484 B s t)). Qed.
Lemma lem5061489 {B : Type'} (s : B -> Prop) : (term182 B s) = (term182 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5061488 B s t)). Qed.
Lemma lem5061490 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5061491 {B : Type'} (s : B -> Prop) : (term183 B s) = (term183 B s).
Proof. exact (MK_COMB (@lem5061490 B) (@lem5061489 B s)). Qed.
Lemma lem5061492 {B : Type'} : (term184 B) = (term184 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5061491 B s)). Qed.
Lemma lem5061493 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5061494 {B : Type'} : (term148 B) = (term148 B).
Proof. exact (MK_COMB (@lem5061493 B) (@lem5061492 B)). Qed.
Lemma lem5061495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061496 {B : Type'} : (term156 B) = (term156 B).
Proof. exact (MK_COMB (@lem5061495) (@lem5061494 B)). Qed.
Lemma lem5061501 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term178 A s x t) = (term178 A s x t).
Proof. exact (eq_refl (term178 A s x t)). Qed.
Lemma lem5061502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term179 A s t) = (term179 A s t).
Proof. exact (fun_ext (fun x : A => @lem5061501 A s x t)). Qed.
Lemma lem5061503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061504 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term180 A s t) = (term180 A s t).
Proof. exact (MK_COMB (@lem5061503 A) (@lem5061502 A s t)). Qed.
Lemma lem5061507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term181 A s t) = (term181 A s t).
Proof. exact (eq_refl (term181 A s t)). Qed.
Lemma lem5061508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term180 A s t)) = ((@SUBSET A s t) = (term180 A s t)).
Proof. exact (MK_COMB (@lem5061507 A s t) (@lem5061504 A s t)). Qed.
Lemma lem5061509 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5061508 A s t)). Qed.
Lemma lem5061510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061511 {A : Type'} (s : A -> Prop) : (term183 A s) = (term183 A s).
Proof. exact (MK_COMB (@lem5061510 A) (@lem5061509 A s)). Qed.
Lemma lem5061512 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5061511 A s)). Qed.
Lemma lem5061513 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061514 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (MK_COMB (@lem5061513 A) (@lem5061512 A)). Qed.
Lemma lem5061515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061516 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (MK_COMB (@lem5061515) (@lem5061514 A)). Qed.
Lemma lem5061517 {A B : Type'} : (term159 A B) = (term159 A B).
Proof. exact (MK_COMB (@lem5061516 A) (@lem5061496 B)). Qed.
Lemma lem5061522 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term185 B y f x s) = (term185 B y f x s).
Proof. exact (eq_refl (term185 B y f x s)). Qed.
Lemma lem5061523 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term186 B y f s) = (term186 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5061522 B y f x s)). Qed.
Lemma lem5061524 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5061525 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term187 B y f s) = (term187 B y f s).
Proof. exact (MK_COMB (@lem5061524 B) (@lem5061523 B y f s)). Qed.
Lemma lem5061528 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term188 B y f s) = (term188 B y f s).
Proof. exact (eq_refl (term188 B y f s)). Qed.
Lemma lem5061529 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term189 B y f s) = (term187 B y f s)) = ((term189 B y f s) = (term187 B y f s)).
Proof. exact (MK_COMB (@lem5061528 B y f s) (@lem5061525 B y f s)). Qed.
Lemma lem5061530 {B : Type'} (y : B) (s : B -> Prop) : (term190 B y s) = (term190 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5061529 B y f s)). Qed.
Lemma lem5061531 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5061532 {B : Type'} (y : B) (s : B -> Prop) : (term191 B y s) = (term191 B y s).
Proof. exact (MK_COMB (@lem5061531 B) (@lem5061530 B y s)). Qed.
Lemma lem5061533 {B : Type'} (y : B) : (term192 B y) = (term192 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5061532 B y s)). Qed.
Lemma lem5061534 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5061535 {B : Type'} (y : B) : (term193 B y) = (term193 B y).
Proof. exact (MK_COMB (@lem5061534 B) (@lem5061533 B y)). Qed.
Lemma lem5061536 {B : Type'} : (term194 B) = (term194 B).
Proof. exact (fun_ext (fun y : B => @lem5061535 B y)). Qed.
Lemma lem5061537 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5061538 {B : Type'} : (term149 B) = (term149 B).
Proof. exact (MK_COMB (@lem5061537 B) (@lem5061536 B)). Qed.
Lemma lem5061539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061540 {B : Type'} : (term160 B) = (term160 B).
Proof. exact (MK_COMB (@lem5061539) (@lem5061538 B)). Qed.
Lemma lem5061541 {A B : Type'} : (term162 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem5061540 B) (@lem5061517 A B)). Qed.
Lemma lem5061546 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term195 A B y f x s) = (term195 A B y f x s).
Proof. exact (eq_refl (term195 A B y f x s)). Qed.
Lemma lem5061547 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term196 A B y f s) = (term196 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5061546 A B y f x s)). Qed.
Lemma lem5061548 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5061549 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term197 A B y f s) = (term197 A B y f s).
Proof. exact (MK_COMB (@lem5061548 A) (@lem5061547 A B y f s)). Qed.
Lemma lem5061552 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term198 A B y f s) = (term198 A B y f s).
Proof. exact (eq_refl (term198 A B y f s)). Qed.
Lemma lem5061553 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term199 A B y f s) = (term197 A B y f s)) = ((term199 A B y f s) = (term197 A B y f s)).
Proof. exact (MK_COMB (@lem5061552 A B y f s) (@lem5061549 A B y f s)). Qed.
Lemma lem5061554 {A B : Type'} (y : B) (s : A -> Prop) : (term200 A B y s) = (term200 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5061553 A B y f s)). Qed.
Lemma lem5061555 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5061556 {A B : Type'} (y : B) (s : A -> Prop) : (term201 A B y s) = (term201 A B y s).
Proof. exact (MK_COMB (@lem5061555 A B) (@lem5061554 A B y s)). Qed.
Lemma lem5061557 {A B : Type'} (y : B) : (term202 A B y) = (term202 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5061556 A B y s)). Qed.
Lemma lem5061558 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061559 {A B : Type'} (y : B) : (term203 A B y) = (term203 A B y).
Proof. exact (MK_COMB (@lem5061558 A) (@lem5061557 A B y)). Qed.
Lemma lem5061560 {A B : Type'} : (term204 A B) = (term204 A B).
Proof. exact (fun_ext (fun y : B => @lem5061559 A B y)). Qed.
Lemma lem5061561 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5061562 {A B : Type'} : (term150 A B) = (term150 A B).
Proof. exact (MK_COMB (@lem5061561 B) (@lem5061560 A B)). Qed.
Lemma lem5061563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061564 {A B : Type'} : (term163 A B) = (term163 A B).
Proof. exact (MK_COMB (@lem5061563) (@lem5061562 A B)). Qed.
Lemma lem5061565 {A B : Type'} : (term165 A B) = (term165 A B).
Proof. exact (MK_COMB (@lem5061564 A B) (@lem5061541 A B)). Qed.
Lemma lem5061570 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term185 A y f x s) = (term185 A y f x s).
Proof. exact (eq_refl (term185 A y f x s)). Qed.
Lemma lem5061571 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term186 A y f s) = (term186 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5061570 A y f x s)). Qed.
Lemma lem5061572 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5061573 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term187 A y f s) = (term187 A y f s).
Proof. exact (MK_COMB (@lem5061572 A) (@lem5061571 A y f s)). Qed.
Lemma lem5061576 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term188 A y f s) = (term188 A y f s).
Proof. exact (eq_refl (term188 A y f s)). Qed.
Lemma lem5061577 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term189 A y f s) = (term187 A y f s)) = ((term189 A y f s) = (term187 A y f s)).
Proof. exact (MK_COMB (@lem5061576 A y f s) (@lem5061573 A y f s)). Qed.
Lemma lem5061578 {A : Type'} (y : A) (s : A -> Prop) : (term190 A y s) = (term190 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5061577 A y f s)). Qed.
Lemma lem5061579 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5061580 {A : Type'} (y : A) (s : A -> Prop) : (term191 A y s) = (term191 A y s).
Proof. exact (MK_COMB (@lem5061579 A) (@lem5061578 A y s)). Qed.
Lemma lem5061581 {A : Type'} (y : A) : (term192 A y) = (term192 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5061580 A y s)). Qed.
Lemma lem5061582 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061583 {A : Type'} (y : A) : (term193 A y) = (term193 A y).
Proof. exact (MK_COMB (@lem5061582 A) (@lem5061581 A y)). Qed.
Lemma lem5061584 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (fun_ext (fun y : A => @lem5061583 A y)). Qed.
Lemma lem5061585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061586 {A : Type'} : (term149 A) = (term149 A).
Proof. exact (MK_COMB (@lem5061585 A) (@lem5061584 A)). Qed.
Lemma lem5061587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061588 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (MK_COMB (@lem5061587) (@lem5061586 A)). Qed.
Lemma lem5061589 {A B : Type'} : (term167 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem5061588 A) (@lem5061565 A B)). Qed.
Lemma lem5061602 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term205 A B s f x y) = (term205 A B s f x y).
Proof. exact (eq_refl (term205 A B s f x y)). Qed.
Lemma lem5061603 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term206 A B s f x) = (term206 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5061602 A B s f x y)). Qed.
Lemma lem5061604 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061605 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term207 A B s f x) = (term207 A B s f x).
Proof. exact (MK_COMB (@lem5061604 A) (@lem5061603 A B s f x)). Qed.
Lemma lem5061606 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term208 A B s f) = (term208 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5061605 A B s f x)). Qed.
Lemma lem5061607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061608 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem5061607 A) (@lem5061606 A B s f)). Qed.
Lemma lem5061613 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term209 A B s f x t) = (term209 A B s f x t).
Proof. exact (eq_refl (term209 A B s f x t)). Qed.
Lemma lem5061614 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term210 A B s f t) = (term210 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5061613 A B s f x t)). Qed.
Lemma lem5061615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061616 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term211 A B s f t) = (term211 A B s f t).
Proof. exact (MK_COMB (@lem5061615 A) (@lem5061614 A B s f t)). Qed.
Lemma lem5061617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5061618 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term138 A B s f t) = (term138 A B s f t).
Proof. exact (MK_COMB (@lem5061617) (@lem5061616 A B s f t)). Qed.
Lemma lem5061619 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term139 A B t s f) = (term139 A B t s f).
Proof. exact (MK_COMB (@lem5061618 A B s f t) (@lem5061608 A B s f)). Qed.
Lemma lem5061632 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term205 A B s f x y) = (term205 A B s f x y).
Proof. exact (eq_refl (term205 A B s f x y)). Qed.
Lemma lem5061633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term206 A B s f x) = (term206 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5061632 A B s f x y)). Qed.
Lemma lem5061634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061635 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term207 A B s f x) = (term207 A B s f x).
Proof. exact (MK_COMB (@lem5061634 A) (@lem5061633 A B s f x)). Qed.
Lemma lem5061636 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term208 A B s f) = (term208 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5061635 A B s f x)). Qed.
Lemma lem5061637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061638 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem5061637 A) (@lem5061636 A B s f)). Qed.
Lemma lem5061641 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term212 A B f s t) = (term212 A B f s t).
Proof. exact (eq_refl (term212 A B f s t)). Qed.
Lemma lem5061642 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term90 A B t s f) = (term90 A B t s f).
Proof. exact (MK_COMB (@lem5061641 A B f s t) (@lem5061638 A B s f)). Qed.
Lemma lem5061643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061644 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term92 A B t s f) = (term92 A B t s f).
Proof. exact (MK_COMB (@lem5061643) (@lem5061642 A B t s f)). Qed.
Lemma lem5061645 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term142 A B t s f) = (term142 A B t s f).
Proof. exact (MK_COMB (@lem5061644 A B t s f) (@lem5061619 A B t s f)). Qed.
Lemma lem5061646 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term143 A B t s) = (term143 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5061645 A B t s f)). Qed.
Lemma lem5061647 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5061648 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term144 A B t s) = (term144 A B t s).
Proof. exact (MK_COMB (@lem5061647 A B) (@lem5061646 A B t s)). Qed.
Lemma lem5061649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061650 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term147 A B t s) = (term147 A B t s).
Proof. exact (MK_COMB (@lem5061649) (@lem5061648 A B t s)). Qed.
Lemma lem5061651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5061652 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term168 A B t s) = (term168 A B t s).
Proof. exact (MK_COMB (@lem5061651) (@lem5061650 A B t s)). Qed.
Lemma lem5061653 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term169 A B t s) = (term169 A B t s).
Proof. exact (MK_COMB (@lem5061652 A B t s) (@lem5061589 A B)). Qed.
Lemma lem5061654 {A B : Type'} (s : A -> Prop) : (term171 A B s) = (term171 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5061653 A B t s)). Qed.
Lemma lem5061655 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5061656 {A B : Type'} (s : A -> Prop) : (term173 A B s) = (term173 A B s).
Proof. exact (MK_COMB (@lem5061655 B) (@lem5061654 A B s)). Qed.
Lemma lem5061657 {A B : Type'} : (term175 A B) = (term175 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5061656 A B s)). Qed.
Lemma lem5061658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5061659 {A B : Type'} : (term177 A B) = (term177 A B).
Proof. exact (MK_COMB (@lem5061658 A) (@lem5061657 A B)). Qed.
Lemma lem5061858 {A B : Type'} : (term176 A B) = (term177 A B).
Proof. exact (TRANS (@lem5061476 A B) (@lem5061659 A B)). Qed.
Lemma lem5061859 {A B : Type'} : (term177 A B) = (term176 A B).
Proof. exact (SYM (@lem5061858 A B)). Qed.
Lemma lem5061860 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term147 A B t s.
Proof. exact (h1). Qed.
Lemma lem5061861 {A : Type'} (h1 : term149 A) : term149 A.
Proof. exact (h1). Qed.
Lemma lem5061862 {A B : Type'} (h1 : term150 A B) : term150 A B.
Proof. exact (h1). Qed.
Lemma lem5061863 {B : Type'} (h1 : term149 B) : term149 B.
Proof. exact (h1). Qed.
Lemma lem5061864 {A : Type'} (h1 : term148 A) : term148 A.
Proof. exact (h1). Qed.
Lemma lem5061865 {B : Type'} (h1 : term148 B) : term148 B.
Proof. exact (h1). Qed.
Lemma lem5061874 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term213 A B s x f y) = (term214 A B s x f y).
Proof. exact (@lem17045 (@IN A y s) ((f x) = (f y))). Qed.
Lemma lem5061876 {A : Type'} (x : A) (s : A -> Prop) : (term215 A x s) = (term215 A x s).
Proof. exact (eq_refl (term215 A x s)). Qed.
Lemma lem5061877 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term216 A B s x f y) = (term217 A B s x f y).
Proof. exact (MK_COMB (@lem5061876 A x s) (@lem5061874 A B s x f y)). Qed.
Lemma lem5061878 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term218 A B s x f y) = (term216 A B s x f y).
Proof. exact (@lem17045 (@IN A x s) (term219 A B s x f y)). Qed.
Lemma lem5061879 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term218 A B s x f y) = (term217 A B s x f y).
Proof. exact (TRANS (@lem5061878 A B s x f y) (@lem5061877 A B s x f y)). Qed.
Lemma lem5061880 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5061881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5061882 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term220 A B s x f y) = (term221 A B s x f y).
Proof. exact (MK_COMB (@lem5061881) (@lem5061879 A B s x f y)). Qed.
Lemma lem5061883 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term222 A B s f x y) = (term223 A B s f x y).
Proof. exact (MK_COMB (@lem5061882 A B s x f y) (@lem5061880 A x y)). Qed.
Lemma lem5061884 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term205 A B s f x y) = (term222 A B s f x y).
Proof. exact (@lem17265 (term224 A B s x f y) (x = y)). Qed.
Lemma lem5061885 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term205 A B s f x y) = (term223 A B s f x y).
Proof. exact (TRANS (@lem5061884 A B s f x y) (@lem5061883 A B s f x y)). Qed.
Lemma lem5061886 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term206 A B s f x) = (term225 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5061885 A B s f x y)). Qed.
Lemma lem5061887 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061888 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term207 A B s f x) = (term226 A B s f x).
Proof. exact (MK_COMB (@lem5061887 A) (@lem5061886 A B s f x)). Qed.
Lemma lem5061889 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term208 A B s f) = (term227 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5061888 A B s f x)). Qed.
Lemma lem5061890 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5061891 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term228 A B s f).
Proof. exact (MK_COMB (@lem5061890 A) (@lem5061889 A B s f)). Qed.
Lemma lem5061893 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term212 A B f s t) = (term212 A B f s t).
Proof. exact (eq_refl (term212 A B f s t)). Qed.
Lemma lem5061894 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term90 A B t s f) = (term229 A B t s f).
Proof. exact (MK_COMB (@lem5061893 A B f s t) (@lem5061891 A B s f)). Qed.
Lemma lem5061901 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term230 A B s f x t) = (term231 A B s f x t).
Proof. exact (@lem17362 (@IN A x s) (term232 A B f x t)). Qed.
Lemma lem5061902 {A : Type'} (P : A -> Prop) : (term233 A P) = (term234 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5061903 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term235 A B s f t) = (term236 A B s f t).
Proof. exact (@lem5061902 A (term210 A B s f t)). Qed.
Lemma lem5061904 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term237 A B s f t x) = (term209 A B s f x t).
Proof. exact (eq_refl (term237 A B s f t x)). Qed.
Lemma lem5061905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061906 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term238 A B s f t x) = (term230 A B s f x t).
Proof. exact (MK_COMB (@lem5061905) (@lem5061904 A B s f x t)). Qed.
Lemma lem5061907 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term238 A B s f t x) = (term231 A B s f x t).
Proof. exact (TRANS (@lem5061906 A B s f x t) (@lem5061901 A B s f x t)). Qed.
Lemma lem5061908 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term239 A B s f t) = (term240 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5061907 A B s f x t)). Qed.
Lemma lem5061909 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5061910 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term236 A B s f t) = (term241 A B s f t).
Proof. exact (MK_COMB (@lem5061909 A) (@lem5061908 A B s f t)). Qed.
Lemma lem5061911 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term235 A B s f t) = (term241 A B s f t).
Proof. exact (TRANS (@lem5061903 A B s f t) (@lem5061910 A B s f t)). Qed.
Lemma lem5061926 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term242 A B s f x y) = (term243 A B s f x y).
Proof. exact (@lem17362 (term224 A B s x f y) (x = y)). Qed.
Lemma lem5061927 {A : Type'} (P : A -> Prop) : (term233 A P) = (term234 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5061928 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term244 A B s f x) = (term245 A B s f x).
Proof. exact (@lem5061927 A (term206 A B s f x)). Qed.
Lemma lem5061929 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term246 A B s f x y) = (term205 A B s f x y).
Proof. exact (eq_refl (term246 A B s f x y)). Qed.
Lemma lem5061930 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061931 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term247 A B s f x y) = (term242 A B s f x y).
Proof. exact (MK_COMB (@lem5061930) (@lem5061929 A B s f x y)). Qed.
Lemma lem5061932 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term247 A B s f x y) = (term243 A B s f x y).
Proof. exact (TRANS (@lem5061931 A B s f x y) (@lem5061926 A B s f x y)). Qed.
Lemma lem5061933 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term248 A B s f x) = (term249 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5061932 A B s f x y)). Qed.
Lemma lem5061934 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5061935 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term245 A B s f x) = (term250 A B s f x).
Proof. exact (MK_COMB (@lem5061934 A) (@lem5061933 A B s f x)). Qed.
Lemma lem5061936 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term244 A B s f x) = (term250 A B s f x).
Proof. exact (TRANS (@lem5061928 A B s f x) (@lem5061935 A B s f x)). Qed.
Lemma lem5061937 {A : Type'} (P : A -> Prop) : (term233 A P) = (term234 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5061938 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term252 A B s f).
Proof. exact (@lem5061937 A (term208 A B s f)). Qed.
Lemma lem5061939 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term253 A B s f x) = (term207 A B s f x).
Proof. exact (eq_refl (term253 A B s f x)). Qed.
Lemma lem5061940 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061941 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term254 A B s f x) = (term244 A B s f x).
Proof. exact (MK_COMB (@lem5061940) (@lem5061939 A B s f x)). Qed.
Lemma lem5061942 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term254 A B s f x) = (term250 A B s f x).
Proof. exact (TRANS (@lem5061941 A B s f x) (@lem5061936 A B s f x)). Qed.
Lemma lem5061943 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term255 A B s f) = (term256 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5061942 A B s f x)). Qed.
Lemma lem5061944 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5061945 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term252 A B s f) = (term257 A B s f).
Proof. exact (MK_COMB (@lem5061944 A) (@lem5061943 A B s f)). Qed.
Lemma lem5061946 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term257 A B s f).
Proof. exact (TRANS (@lem5061938 A B s f) (@lem5061945 A B s f)). Qed.
Lemma lem5061947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5061948 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term258 A B s f t) = (term259 A B s f t).
Proof. exact (MK_COMB (@lem5061947) (@lem5061911 A B s f t)). Qed.
Lemma lem5061949 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term260 A B t s f) = (term261 A B t s f).
Proof. exact (MK_COMB (@lem5061948 A B s f t) (@lem5061946 A B s f)). Qed.
Lemma lem5061950 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term262 A B t s f) = (term260 A B t s f).
Proof. exact (@lem17045 (term211 A B s f t) (term118 A B s f)). Qed.
Lemma lem5061951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term262 A B t s f) = (term261 A B t s f).
Proof. exact (TRANS (@lem5061950 A B t s f) (@lem5061949 A B t s f)). Qed.
Lemma lem5061952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5061953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term263 A B t s f) = (term264 A B t s f).
Proof. exact (MK_COMB (@lem5061952) (@lem5061894 A B t s f)). Qed.
Lemma lem5061954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term265 A B t s f) = (term266 A B t s f).
Proof. exact (MK_COMB (@lem5061953 A B t s f) (@lem5061951 A B t s f)). Qed.
Lemma lem5061955 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term267 A B t s f) = (term265 A B t s f).
Proof. exact (@lem17362 (term90 A B t s f) (term139 A B t s f)). Qed.
Lemma lem5061956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term267 A B t s f) = (term266 A B t s f).
Proof. exact (TRANS (@lem5061955 A B t s f) (@lem5061954 A B t s f)). Qed.
Lemma lem5061957 {A B : Type'} (P : type572 A B) : (term268 A B P) = (term269 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem5061958 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term147 A B t s) = (term270 A B t s).
Proof. exact (@lem5061957 A B (term143 A B t s)). Qed.
Lemma lem5061959 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term271 A B t s f) = (term142 A B t s f).
Proof. exact (eq_refl (term271 A B t s f)). Qed.
Lemma lem5061960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5061961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term272 A B t s f) = (term267 A B t s f).
Proof. exact (MK_COMB (@lem5061960) (@lem5061959 A B t s f)). Qed.
Lemma lem5061962 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term272 A B t s f) = (term266 A B t s f).
Proof. exact (TRANS (@lem5061961 A B t s f) (@lem5061956 A B t s f)). Qed.
Lemma lem5061963 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term273 A B t s) = (term274 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5061962 A B t s f)). Qed.
Lemma lem5061964 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5061965 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term270 A B t s) = (term275 A B t s).
Proof. exact (MK_COMB (@lem5061964 A B) (@lem5061963 A B t s)). Qed.
Lemma lem5061966 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term147 A B t s) = (term275 A B t s).
Proof. exact (TRANS (@lem5061958 A B t s) (@lem5061965 A B t s)). Qed.
Lemma lem5062169 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5062170 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (@lem5062169 A P Q). Qed.
Lemma lem5062171 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term278 A B t s f) = (term279 A B t s f).
Proof. exact (@lem5062170 A (term240 A B s f t) (term256 A B s f)). Qed.
Lemma lem5062172 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term280 A B s f t x) = (term231 A B s f x t).
Proof. exact (eq_refl (term280 A B s f t x)). Qed.
Lemma lem5062173 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term281 A B s f t) = (term240 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5062172 A B s f x t)). Qed.
Lemma lem5062174 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062175 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term282 A B s f t) = (term241 A B s f t).
Proof. exact (MK_COMB (@lem5062174 A) (@lem5062173 A B s f t)). Qed.
Lemma lem5062176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5062177 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term283 A B s f t) = (term259 A B s f t).
Proof. exact (MK_COMB (@lem5062176) (@lem5062175 A B s f t)). Qed.
Lemma lem5062178 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term284 A B s f x) = (term250 A B s f x).
Proof. exact (eq_refl (term284 A B s f x)). Qed.
Lemma lem5062179 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term285 A B s f) = (term256 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5062178 A B s f x)). Qed.
Lemma lem5062180 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062181 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term286 A B s f) = (term257 A B s f).
Proof. exact (MK_COMB (@lem5062180 A) (@lem5062179 A B s f)). Qed.
Lemma lem5062182 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term278 A B t s f) = (term261 A B t s f).
Proof. exact (MK_COMB (@lem5062177 A B s f t) (@lem5062181 A B s f)). Qed.
Lemma lem5062183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term287 A B t s f) = (term288 A B t s f).
Proof. exact (MK_COMB (@lem5062183) (@lem5062182 A B t s f)). Qed.
Lemma lem5062185 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term280 A B s f t x) = (term231 A B s f x t).
Proof. exact (eq_refl (term280 A B s f t x)). Qed.
Lemma lem5062186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5062187 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term289 A B s f t x) = (term290 A B s f x t).
Proof. exact (MK_COMB (@lem5062186) (@lem5062185 A B s f x t)). Qed.
Lemma lem5062188 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term284 A B s f x) = (term250 A B s f x).
Proof. exact (eq_refl (term284 A B s f x)). Qed.
Lemma lem5062189 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term291 A B t s f x) = (term292 A B t s f x).
Proof. exact (MK_COMB (@lem5062187 A B s f x t) (@lem5062188 A B s f x)). Qed.
Lemma lem5062190 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term293 A B t s f) = (term294 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem5062189 A B t s f x)). Qed.
Lemma lem5062191 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062192 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term279 A B t s f) = (term295 A B t s f).
Proof. exact (MK_COMB (@lem5062191 A) (@lem5062190 A B t s f)). Qed.
Lemma lem5062193 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term278 A B t s f) = (term279 A B t s f)) = ((term261 A B t s f) = (term295 A B t s f)).
Proof. exact (MK_COMB (@lem5062184 A B t s f) (@lem5062192 A B t s f)). Qed.
Lemma lem5062194 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term261 A B t s f) = (term295 A B t s f).
Proof. exact (EQ_MP (@lem5062193 A B t s f) (@lem5062171 A B t s f)). Qed.
Lemma lem5062196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5062197 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem5062196 A P Q). Qed.
Lemma lem5062198 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term298 A B t s f x) = (term299 A B t s f x).
Proof. exact (@lem5062197 A (term231 A B s f x t) (term249 A B s f x)). Qed.
Lemma lem5062199 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term300 A B s f x y) = (term243 A B s f x y).
Proof. exact (eq_refl (term300 A B s f x y)). Qed.
Lemma lem5062200 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term301 A B s f x) = (term249 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5062199 A B s f x y)). Qed.
Lemma lem5062201 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062202 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term302 A B s f x) = (term250 A B s f x).
Proof. exact (MK_COMB (@lem5062201 A) (@lem5062200 A B s f x)). Qed.
Lemma lem5062203 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term290 A B s f x t) = (term290 A B s f x t).
Proof. exact (eq_refl (term290 A B s f x t)). Qed.
Lemma lem5062204 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term298 A B t s f x) = (term292 A B t s f x).
Proof. exact (MK_COMB (@lem5062203 A B s f x t) (@lem5062202 A B s f x)). Qed.
Lemma lem5062205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062206 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term303 A B t s f x) = (term304 A B t s f x).
Proof. exact (MK_COMB (@lem5062205) (@lem5062204 A B t s f x)). Qed.
Lemma lem5062207 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term300 A B s f x y) = (term243 A B s f x y).
Proof. exact (eq_refl (term300 A B s f x y)). Qed.
Lemma lem5062208 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term290 A B s f x t) = (term290 A B s f x t).
Proof. exact (eq_refl (term290 A B s f x t)). Qed.
Lemma lem5062209 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term305 A B t s f x y) = (term306 A B t s f x y).
Proof. exact (MK_COMB (@lem5062208 A B s f x t) (@lem5062207 A B s f x y)). Qed.
Lemma lem5062210 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term307 A B t s f x) = (term308 A B t s f x).
Proof. exact (fun_ext (fun y : A => @lem5062209 A B t s f x y)). Qed.
Lemma lem5062211 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062212 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term299 A B t s f x) = (term309 A B t s f x).
Proof. exact (MK_COMB (@lem5062211 A) (@lem5062210 A B t s f x)). Qed.
Lemma lem5062213 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term298 A B t s f x) = (term299 A B t s f x)) = ((term292 A B t s f x) = (term309 A B t s f x)).
Proof. exact (MK_COMB (@lem5062206 A B t s f x) (@lem5062212 A B t s f x)). Qed.
Lemma lem5062214 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term292 A B t s f x) = (term309 A B t s f x).
Proof. exact (EQ_MP (@lem5062213 A B t s f x) (@lem5062198 A B t s f x)). Qed.
Lemma lem5062215 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term294 A B t s f) = (term310 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem5062214 A B t s f x)). Qed.
Lemma lem5062216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062217 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term295 A B t s f) = (term311 A B t s f).
Proof. exact (MK_COMB (@lem5062216 A) (@lem5062215 A B t s f)). Qed.
Lemma lem5062218 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term261 A B t s f) = (term311 A B t s f).
Proof. exact (TRANS (@lem5062194 A B t s f) (@lem5062217 A B t s f)). Qed.
Lemma lem5062219 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term264 A B t s f).
Proof. exact (eq_refl (term264 A B t s f)). Qed.
Lemma lem5062220 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term266 A B t s f) = (term312 A B t s f).
Proof. exact (MK_COMB (@lem5062219 A B t s f) (@lem5062218 A B t s f)). Qed.
Lemma lem5062222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5062223 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem5062222 A P Q). Qed.
Lemma lem5062224 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term315 A B t s f) = (term316 A B t s f).
Proof. exact (@lem5062223 A (term229 A B t s f) (term310 A B t s f)). Qed.
Lemma lem5062225 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term317 A B t s f x) = (term309 A B t s f x).
Proof. exact (eq_refl (term317 A B t s f x)). Qed.
Lemma lem5062226 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term318 A B t s f) = (term310 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem5062225 A B t s f x)). Qed.
Lemma lem5062227 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062228 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term319 A B t s f) = (term311 A B t s f).
Proof. exact (MK_COMB (@lem5062227 A) (@lem5062226 A B t s f)). Qed.
Lemma lem5062229 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term264 A B t s f).
Proof. exact (eq_refl (term264 A B t s f)). Qed.
Lemma lem5062230 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term315 A B t s f) = (term312 A B t s f).
Proof. exact (MK_COMB (@lem5062229 A B t s f) (@lem5062228 A B t s f)). Qed.
Lemma lem5062231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062232 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term320 A B t s f) = (term321 A B t s f).
Proof. exact (MK_COMB (@lem5062231) (@lem5062230 A B t s f)). Qed.
Lemma lem5062233 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term317 A B t s f x) = (term309 A B t s f x).
Proof. exact (eq_refl (term317 A B t s f x)). Qed.
Lemma lem5062234 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term264 A B t s f).
Proof. exact (eq_refl (term264 A B t s f)). Qed.
Lemma lem5062235 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term322 A B t s f x) = (term323 A B t s f x).
Proof. exact (MK_COMB (@lem5062234 A B t s f) (@lem5062233 A B t s f x)). Qed.
Lemma lem5062236 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term324 A B t s f) = (term325 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem5062235 A B t s f x)). Qed.
Lemma lem5062237 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062238 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term316 A B t s f) = (term326 A B t s f).
Proof. exact (MK_COMB (@lem5062237 A) (@lem5062236 A B t s f)). Qed.
Lemma lem5062239 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term315 A B t s f) = (term316 A B t s f)) = ((term312 A B t s f) = (term326 A B t s f)).
Proof. exact (MK_COMB (@lem5062232 A B t s f) (@lem5062238 A B t s f)). Qed.
Lemma lem5062240 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term312 A B t s f) = (term326 A B t s f).
Proof. exact (EQ_MP (@lem5062239 A B t s f) (@lem5062224 A B t s f)). Qed.
Lemma lem5062242 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5062243 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem5062242 A P Q). Qed.
Lemma lem5062244 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term327 A B t s f x) = (term328 A B t s f x).
Proof. exact (@lem5062243 A (term229 A B t s f) (term308 A B t s f x)). Qed.
Lemma lem5062245 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term329 A B t s f x y) = (term306 A B t s f x y).
Proof. exact (eq_refl (term329 A B t s f x y)). Qed.
Lemma lem5062246 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term330 A B t s f x) = (term308 A B t s f x).
Proof. exact (fun_ext (fun y : A => @lem5062245 A B t s f x y)). Qed.
Lemma lem5062247 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062248 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term331 A B t s f x) = (term309 A B t s f x).
Proof. exact (MK_COMB (@lem5062247 A) (@lem5062246 A B t s f x)). Qed.
Lemma lem5062249 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term264 A B t s f).
Proof. exact (eq_refl (term264 A B t s f)). Qed.
Lemma lem5062250 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term327 A B t s f x) = (term323 A B t s f x).
Proof. exact (MK_COMB (@lem5062249 A B t s f) (@lem5062248 A B t s f x)). Qed.
Lemma lem5062251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062252 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term332 A B t s f x) = (term333 A B t s f x).
Proof. exact (MK_COMB (@lem5062251) (@lem5062250 A B t s f x)). Qed.
Lemma lem5062253 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term329 A B t s f x y) = (term306 A B t s f x y).
Proof. exact (eq_refl (term329 A B t s f x y)). Qed.
Lemma lem5062254 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term264 A B t s f).
Proof. exact (eq_refl (term264 A B t s f)). Qed.
Lemma lem5062255 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term334 A B t s f x y) = (term335 A B t s f x y).
Proof. exact (MK_COMB (@lem5062254 A B t s f) (@lem5062253 A B t s f x y)). Qed.
Lemma lem5062256 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term336 A B t s f x) = (term337 A B t s f x).
Proof. exact (fun_ext (fun y : A => @lem5062255 A B t s f x y)). Qed.
Lemma lem5062257 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062258 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term328 A B t s f x) = (term338 A B t s f x).
Proof. exact (MK_COMB (@lem5062257 A) (@lem5062256 A B t s f x)). Qed.
Lemma lem5062259 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term327 A B t s f x) = (term328 A B t s f x)) = ((term323 A B t s f x) = (term338 A B t s f x)).
Proof. exact (MK_COMB (@lem5062252 A B t s f x) (@lem5062258 A B t s f x)). Qed.
Lemma lem5062260 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term323 A B t s f x) = (term338 A B t s f x).
Proof. exact (EQ_MP (@lem5062259 A B t s f x) (@lem5062244 A B t s f x)). Qed.
Lemma lem5062261 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term325 A B t s f) = (term339 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem5062260 A B t s f x)). Qed.
Lemma lem5062262 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062263 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term326 A B t s f) = (term340 A B t s f).
Proof. exact (MK_COMB (@lem5062262 A) (@lem5062261 A B t s f)). Qed.
Lemma lem5062264 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term312 A B t s f) = (term340 A B t s f).
Proof. exact (TRANS (@lem5062240 A B t s f) (@lem5062263 A B t s f)). Qed.
Lemma lem5062265 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term266 A B t s f) = (term340 A B t s f).
Proof. exact (TRANS (@lem5062220 A B t s f) (@lem5062264 A B t s f)). Qed.
Lemma lem5062266 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term274 A B t s) = (term341 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5062265 A B t s f)). Qed.
Lemma lem5062267 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5062269 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term275 A B t s) = (term342 A B t s).
Proof. exact (MK_COMB (@lem5062267 A B) (@lem5062266 A B t s)). Qed.
Lemma lem5062270 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term147 A B t s) = (term342 A B t s).
Proof. exact (TRANS (@lem5061966 A B t s) (@lem5062269 A B t s)). Qed.
Lemma lem5062271 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term342 A B t s.
Proof. exact (EQ_MP (@lem5062270 A B t s) (@lem5061860 A B t s h1)). Qed.
Lemma lem5062282 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term343 A y f x s) = (term344 A y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem5062285 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term185 A y f x s) = (term185 A y f x s).
Proof. exact (eq_refl (term185 A y f x s)). Qed.
Lemma lem5062286 {A : Type'} (P : A -> Prop) : (term345 A P) = (term346 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5062287 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term347 A y f s) = (term348 A y f s).
Proof. exact (@lem5062286 A (term186 A y f s)). Qed.
Lemma lem5062288 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term349 A y f s x) = (term185 A y f x s).
Proof. exact (eq_refl (term349 A y f s x)). Qed.
Lemma lem5062289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5062290 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term350 A y f s x) = (term343 A y f x s).
Proof. exact (MK_COMB (@lem5062289) (@lem5062288 A y f x s)). Qed.
Lemma lem5062291 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term350 A y f s x) = (term344 A y f x s).
Proof. exact (TRANS (@lem5062290 A y f x s) (@lem5062282 A y f x s)). Qed.
Lemma lem5062292 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term351 A y f s) = (term352 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5062291 A y f x s)). Qed.
Lemma lem5062293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062294 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term348 A y f s) = (term353 A y f s).
Proof. exact (MK_COMB (@lem5062293 A) (@lem5062292 A y f s)). Qed.
Lemma lem5062295 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term347 A y f s) = (term353 A y f s).
Proof. exact (TRANS (@lem5062287 A y f s) (@lem5062294 A y f s)). Qed.
Lemma lem5062296 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term186 A y f s) = (term186 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5062285 A y f x s)). Qed.
Lemma lem5062297 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5062298 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term187 A y f s) = (term187 A y f s).
Proof. exact (MK_COMB (@lem5062297 A) (@lem5062296 A y f s)). Qed.
Lemma lem5062300 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term354 A y f s) = (term354 A y f s).
Proof. exact (eq_refl (term354 A y f s)). Qed.
Lemma lem5062301 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term355 A y f s) = (term355 A y f s).
Proof. exact (MK_COMB (@lem5062300 A y f s) (@lem5062298 A y f s)). Qed.
Lemma lem5062303 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term356 A y f s) = (term356 A y f s).
Proof. exact (eq_refl (term356 A y f s)). Qed.
Lemma lem5062304 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term357 A y f s) = (term358 A y f s).
Proof. exact (MK_COMB (@lem5062303 A y f s) (@lem5062295 A y f s)). Qed.
Lemma lem5062305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062306 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term359 A y f s) = (term360 A y f s).
Proof. exact (MK_COMB (@lem5062305) (@lem5062304 A y f s)). Qed.
Lemma lem5062307 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term361 A y f s) = (term362 A y f s).
Proof. exact (MK_COMB (@lem5062306 A y f s) (@lem5062301 A y f s)). Qed.
Lemma lem5062308 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term189 A y f s) = (term187 A y f s)) = (term361 A y f s).
Proof. exact (@lem17784 (term189 A y f s) (term187 A y f s)). Qed.
Lemma lem5062309 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term189 A y f s) = (term187 A y f s)) = (term362 A y f s).
Proof. exact (TRANS (@lem5062308 A y f s) (@lem5062307 A y f s)). Qed.
Lemma lem5062310 {A : Type'} (y : A) (s : A -> Prop) : (term190 A y s) = (term363 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5062309 A y f s)). Qed.
Lemma lem5062311 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5062312 {A : Type'} (y : A) (s : A -> Prop) : (term191 A y s) = (term364 A y s).
Proof. exact (MK_COMB (@lem5062311 A) (@lem5062310 A y s)). Qed.
Lemma lem5062313 {A : Type'} (y : A) : (term192 A y) = (term365 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5062312 A y s)). Qed.
Lemma lem5062314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5062315 {A : Type'} (y : A) : (term193 A y) = (term366 A y).
Proof. exact (MK_COMB (@lem5062314 A) (@lem5062313 A y)). Qed.
Lemma lem5062316 {A : Type'} : (term194 A) = (term367 A).
Proof. exact (fun_ext (fun y : A => @lem5062315 A y)). Qed.
Lemma lem5062317 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062318 {A : Type'} : (term149 A) = (term368 A).
Proof. exact (MK_COMB (@lem5062317 A) (@lem5062316 A)). Qed.
Lemma lem5062328 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5062329 {A : Type'} (P : type488 A) (Q : type488 A) : (term371 A P Q) = (term372 A P Q).
Proof. exact (@lem5062328 (A -> A) P Q). Qed.
Lemma lem5062330 {A : Type'} (y : A) (s : A -> Prop) : (term373 A y s) = (term374 A y s).
Proof. exact (@lem5062329 A (term375 A y s) (term376 A y s)). Qed.
Lemma lem5062331 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term377 A y s f) = (term358 A y f s).
Proof. exact (eq_refl (term377 A y s f)). Qed.
Lemma lem5062332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062333 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term378 A y s f) = (term360 A y f s).
Proof. exact (MK_COMB (@lem5062332) (@lem5062331 A y f s)). Qed.
Lemma lem5062334 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term379 A y s f) = (term355 A y f s).
Proof. exact (eq_refl (term379 A y s f)). Qed.
Lemma lem5062335 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term380 A y s f) = (term362 A y f s).
Proof. exact (MK_COMB (@lem5062333 A y f s) (@lem5062334 A y f s)). Qed.
Lemma lem5062336 {A : Type'} (y : A) (s : A -> Prop) : (term381 A y s) = (term363 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5062335 A y f s)). Qed.
Lemma lem5062337 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5062338 {A : Type'} (y : A) (s : A -> Prop) : (term373 A y s) = (term364 A y s).
Proof. exact (MK_COMB (@lem5062337 A) (@lem5062336 A y s)). Qed.
Lemma lem5062339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062340 {A : Type'} (y : A) (s : A -> Prop) : (term382 A y s) = (term383 A y s).
Proof. exact (MK_COMB (@lem5062339) (@lem5062338 A y s)). Qed.
Lemma lem5062341 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term377 A y s f) = (term358 A y f s).
Proof. exact (eq_refl (term377 A y s f)). Qed.
Lemma lem5062342 {A : Type'} (y : A) (s : A -> Prop) : (term384 A y s) = (term375 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5062341 A y f s)). Qed.
Lemma lem5062343 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5062344 {A : Type'} (y : A) (s : A -> Prop) : (term385 A y s) = (term386 A y s).
Proof. exact (MK_COMB (@lem5062343 A) (@lem5062342 A y s)). Qed.
Lemma lem5062345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062346 {A : Type'} (y : A) (s : A -> Prop) : (term387 A y s) = (term388 A y s).
Proof. exact (MK_COMB (@lem5062345) (@lem5062344 A y s)). Qed.
Lemma lem5062347 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term379 A y s f) = (term355 A y f s).
Proof. exact (eq_refl (term379 A y s f)). Qed.
Lemma lem5062348 {A : Type'} (y : A) (s : A -> Prop) : (term389 A y s) = (term376 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5062347 A y f s)). Qed.
Lemma lem5062349 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5062350 {A : Type'} (y : A) (s : A -> Prop) : (term390 A y s) = (term391 A y s).
Proof. exact (MK_COMB (@lem5062349 A) (@lem5062348 A y s)). Qed.
Lemma lem5062351 {A : Type'} (y : A) (s : A -> Prop) : (term374 A y s) = (term392 A y s).
Proof. exact (MK_COMB (@lem5062346 A y s) (@lem5062350 A y s)). Qed.
Lemma lem5062352 {A : Type'} (y : A) (s : A -> Prop) : ((term373 A y s) = (term374 A y s)) = ((term364 A y s) = (term392 A y s)).
Proof. exact (MK_COMB (@lem5062340 A y s) (@lem5062351 A y s)). Qed.
Lemma lem5062353 {A : Type'} (y : A) (s : A -> Prop) : (term364 A y s) = (term392 A y s).
Proof. exact (EQ_MP (@lem5062352 A y s) (@lem5062330 A y s)). Qed.
Lemma lem5062546 {A : Type'} (y : A) : (term365 A y) = (term393 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5062353 A y s)). Qed.
Lemma lem5062547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5062548 {A : Type'} (y : A) : (term366 A y) = (term394 A y).
Proof. exact (MK_COMB (@lem5062547 A) (@lem5062546 A y)). Qed.
Lemma lem5062550 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5062551 {A : Type'} (P : type686 A) (Q : type686 A) : (term395 A P Q) = (term396 A P Q).
Proof. exact (@lem5062550 (A -> Prop) P Q). Qed.
Lemma lem5062552 {A : Type'} (y : A) : (term397 A y) = (term398 A y).
Proof. exact (@lem5062551 A (term399 A y) (term400 A y)). Qed.
Lemma lem5062553 {A : Type'} (y : A) (s : A -> Prop) : (term401 A y s) = (term386 A y s).
Proof. exact (eq_refl (term401 A y s)). Qed.
Lemma lem5062554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062555 {A : Type'} (y : A) (s : A -> Prop) : (term402 A y s) = (term388 A y s).
Proof. exact (MK_COMB (@lem5062554) (@lem5062553 A y s)). Qed.
Lemma lem5062556 {A : Type'} (y : A) (s : A -> Prop) : (term403 A y s) = (term391 A y s).
Proof. exact (eq_refl (term403 A y s)). Qed.
Lemma lem5062557 {A : Type'} (y : A) (s : A -> Prop) : (term404 A y s) = (term392 A y s).
Proof. exact (MK_COMB (@lem5062555 A y s) (@lem5062556 A y s)). Qed.
Lemma lem5062558 {A : Type'} (y : A) : (term405 A y) = (term393 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5062557 A y s)). Qed.
Lemma lem5062559 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5062560 {A : Type'} (y : A) : (term397 A y) = (term394 A y).
Proof. exact (MK_COMB (@lem5062559 A) (@lem5062558 A y)). Qed.
Lemma lem5062561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062562 {A : Type'} (y : A) : (term406 A y) = (term407 A y).
Proof. exact (MK_COMB (@lem5062561) (@lem5062560 A y)). Qed.
Lemma lem5062563 {A : Type'} (y : A) (s : A -> Prop) : (term401 A y s) = (term386 A y s).
Proof. exact (eq_refl (term401 A y s)). Qed.
Lemma lem5062564 {A : Type'} (y : A) : (term408 A y) = (term399 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5062563 A y s)). Qed.
Lemma lem5062565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5062566 {A : Type'} (y : A) : (term409 A y) = (term410 A y).
Proof. exact (MK_COMB (@lem5062565 A) (@lem5062564 A y)). Qed.
Lemma lem5062567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062568 {A : Type'} (y : A) : (term411 A y) = (term412 A y).
Proof. exact (MK_COMB (@lem5062567) (@lem5062566 A y)). Qed.
Lemma lem5062569 {A : Type'} (y : A) (s : A -> Prop) : (term403 A y s) = (term391 A y s).
Proof. exact (eq_refl (term403 A y s)). Qed.
Lemma lem5062570 {A : Type'} (y : A) : (term413 A y) = (term400 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5062569 A y s)). Qed.
Lemma lem5062571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5062572 {A : Type'} (y : A) : (term414 A y) = (term415 A y).
Proof. exact (MK_COMB (@lem5062571 A) (@lem5062570 A y)). Qed.
Lemma lem5062573 {A : Type'} (y : A) : (term398 A y) = (term416 A y).
Proof. exact (MK_COMB (@lem5062568 A y) (@lem5062572 A y)). Qed.
Lemma lem5062574 {A : Type'} (y : A) : ((term397 A y) = (term398 A y)) = ((term394 A y) = (term416 A y)).
Proof. exact (MK_COMB (@lem5062562 A y) (@lem5062573 A y)). Qed.
Lemma lem5062575 {A : Type'} (y : A) : (term394 A y) = (term416 A y).
Proof. exact (EQ_MP (@lem5062574 A y) (@lem5062552 A y)). Qed.
Lemma lem5062776 {A : Type'} (y : A) : (term366 A y) = (term416 A y).
Proof. exact (TRANS (@lem5062548 A y) (@lem5062575 A y)). Qed.
Lemma lem5062777 {A : Type'} : (term367 A) = (term417 A).
Proof. exact (fun_ext (fun y : A => @lem5062776 A y)). Qed.
Lemma lem5062778 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062779 {A : Type'} : (term368 A) = (term418 A).
Proof. exact (MK_COMB (@lem5062778 A) (@lem5062777 A)). Qed.
Lemma lem5062781 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5062782 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (@lem5062781 A P Q). Qed.
Lemma lem5062783 {A : Type'} : (term419 A) = (term420 A).
Proof. exact (@lem5062782 A (term421 A) (term422 A)). Qed.
Lemma lem5062784 {A : Type'} (y : A) : (term423 A y) = (term410 A y).
Proof. exact (eq_refl (term423 A y)). Qed.
Lemma lem5062785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062786 {A : Type'} (y : A) : (term424 A y) = (term412 A y).
Proof. exact (MK_COMB (@lem5062785) (@lem5062784 A y)). Qed.
Lemma lem5062787 {A : Type'} (y : A) : (term425 A y) = (term415 A y).
Proof. exact (eq_refl (term425 A y)). Qed.
Lemma lem5062788 {A : Type'} (y : A) : (term426 A y) = (term416 A y).
Proof. exact (MK_COMB (@lem5062786 A y) (@lem5062787 A y)). Qed.
Lemma lem5062789 {A : Type'} : (term427 A) = (term417 A).
Proof. exact (fun_ext (fun y : A => @lem5062788 A y)). Qed.
Lemma lem5062790 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062791 {A : Type'} : (term419 A) = (term418 A).
Proof. exact (MK_COMB (@lem5062790 A) (@lem5062789 A)). Qed.
Lemma lem5062792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5062793 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (MK_COMB (@lem5062792) (@lem5062791 A)). Qed.
Lemma lem5062794 {A : Type'} (y : A) : (term423 A y) = (term410 A y).
Proof. exact (eq_refl (term423 A y)). Qed.
Lemma lem5062795 {A : Type'} : (term430 A) = (term421 A).
Proof. exact (fun_ext (fun y : A => @lem5062794 A y)). Qed.
Lemma lem5062796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062797 {A : Type'} : (term431 A) = (term432 A).
Proof. exact (MK_COMB (@lem5062796 A) (@lem5062795 A)). Qed.
Lemma lem5062798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5062799 {A : Type'} : (term433 A) = (term434 A).
Proof. exact (MK_COMB (@lem5062798) (@lem5062797 A)). Qed.
Lemma lem5062800 {A : Type'} (y : A) : (term425 A y) = (term415 A y).
Proof. exact (eq_refl (term425 A y)). Qed.
Lemma lem5062801 {A : Type'} : (term435 A) = (term422 A).
Proof. exact (fun_ext (fun y : A => @lem5062800 A y)). Qed.
Lemma lem5062802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5062803 {A : Type'} : (term436 A) = (term437 A).
Proof. exact (MK_COMB (@lem5062802 A) (@lem5062801 A)). Qed.
Lemma lem5062804 {A : Type'} : (term420 A) = (term438 A).
Proof. exact (MK_COMB (@lem5062799 A) (@lem5062803 A)). Qed.
Lemma lem5062805 {A : Type'} : ((term419 A) = (term420 A)) = ((term418 A) = (term438 A)).
Proof. exact (MK_COMB (@lem5062793 A) (@lem5062804 A)). Qed.
Lemma lem5062806 {A : Type'} : (term418 A) = (term438 A).
Proof. exact (EQ_MP (@lem5062805 A) (@lem5062783 A)). Qed.
Lemma lem5063015 {A : Type'} : (term368 A) = (term438 A).
Proof. exact (TRANS (@lem5062779 A) (@lem5062806 A)). Qed.
Lemma lem5063017 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5063018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem5063017 A P Q). Qed.
Lemma lem5063019 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term439 A y f s) = (term440 A y f s).
Proof. exact (@lem5063018 A (term441 A y f s) (term186 A y f s)). Qed.
Lemma lem5063020 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term349 A y f s x) = (term185 A y f x s).
Proof. exact (eq_refl (term349 A y f s x)). Qed.
Lemma lem5063021 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term442 A y f s) = (term186 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5063020 A y f x s)). Qed.
Lemma lem5063022 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063023 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term443 A y f s) = (term187 A y f s).
Proof. exact (MK_COMB (@lem5063022 A) (@lem5063021 A y f s)). Qed.
Lemma lem5063024 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term354 A y f s) = (term354 A y f s).
Proof. exact (eq_refl (term354 A y f s)). Qed.
Lemma lem5063025 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term439 A y f s) = (term355 A y f s).
Proof. exact (MK_COMB (@lem5063024 A y f s) (@lem5063023 A y f s)). Qed.
Lemma lem5063026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063027 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term444 A y f s) = (term445 A y f s).
Proof. exact (MK_COMB (@lem5063026) (@lem5063025 A y f s)). Qed.
Lemma lem5063028 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term349 A y f s x) = (term185 A y f x s).
Proof. exact (eq_refl (term349 A y f s x)). Qed.
Lemma lem5063029 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term354 A y f s) = (term354 A y f s).
Proof. exact (eq_refl (term354 A y f s)). Qed.
Lemma lem5063030 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term446 A y f s x) = (term447 A y f x s).
Proof. exact (MK_COMB (@lem5063029 A y f s) (@lem5063028 A y f x s)). Qed.
Lemma lem5063031 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term448 A y f s) = (term449 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5063030 A y f x s)). Qed.
Lemma lem5063032 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063033 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term440 A y f s) = (term450 A y f s).
Proof. exact (MK_COMB (@lem5063032 A) (@lem5063031 A y f s)). Qed.
Lemma lem5063034 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term439 A y f s) = (term440 A y f s)) = ((term355 A y f s) = (term450 A y f s)).
Proof. exact (MK_COMB (@lem5063027 A y f s) (@lem5063033 A y f s)). Qed.
Lemma lem5063035 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term355 A y f s) = (term450 A y f s).
Proof. exact (EQ_MP (@lem5063034 A y f s) (@lem5063019 A y f s)). Qed.
Lemma lem5063036 {A : Type'} (y : A) (s : A -> Prop) : (term376 A y s) = (term451 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5063035 A y f s)). Qed.
Lemma lem5063037 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5063038 {A : Type'} (y : A) (s : A -> Prop) : (term391 A y s) = (term452 A y s).
Proof. exact (MK_COMB (@lem5063037 A) (@lem5063036 A y s)). Qed.
Lemma lem5063040 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5063041 {A : Type'} (P : type486 A) : (term455 A P) = (term456 A P).
Proof. exact (@lem5063040 (A -> A) A P). Qed.
Lemma lem5063042 {A : Type'} (y : A) (s : A -> Prop) : (term457 A y s) = (term458 A y s).
Proof. exact (@lem5063041 A (term459 A y s)). Qed.
Lemma lem5063043 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term460 A y s f) = (term449 A y f s).
Proof. exact (eq_refl (term460 A y s f)). Qed.
Lemma lem5063044 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5063045 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) (x : A) : (term461 A y s f x) = (term462 A y f s x).
Proof. exact (MK_COMB (@lem5063043 A y f s) (@lem5063044 A x)). Qed.
Lemma lem5063046 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term462 A y f s x) = (term447 A y f x s).
Proof. exact (eq_refl (term462 A y f s x)). Qed.
Lemma lem5063047 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term461 A y s f x) = (term447 A y f x s).
Proof. exact (TRANS (@lem5063045 A y f s x) (@lem5063046 A y f x s)). Qed.
Lemma lem5063048 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term463 A y s f) = (term449 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5063047 A y f x s)). Qed.
Lemma lem5063049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063050 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term464 A y s f) = (term450 A y f s).
Proof. exact (MK_COMB (@lem5063049 A) (@lem5063048 A y f s)). Qed.
Lemma lem5063051 {A : Type'} (y : A) (s : A -> Prop) : (term465 A y s) = (term451 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5063050 A y f s)). Qed.
Lemma lem5063052 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5063053 {A : Type'} (y : A) (s : A -> Prop) : (term457 A y s) = (term452 A y s).
Proof. exact (MK_COMB (@lem5063052 A) (@lem5063051 A y s)). Qed.
Lemma lem5063054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063055 {A : Type'} (y : A) (s : A -> Prop) : (term466 A y s) = (term467 A y s).
Proof. exact (MK_COMB (@lem5063054) (@lem5063053 A y s)). Qed.
Lemma lem5063056 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term460 A y s f) = (term449 A y f s).
Proof. exact (eq_refl (term460 A y s f)). Qed.
Lemma lem5063057 {A : Type'} (x : type487 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5063058 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) (f : A -> A) : (term468 A y s x f) = (term469 A y s x f).
Proof. exact (MK_COMB (@lem5063056 A y f s) (@lem5063057 A x f)). Qed.
Lemma lem5063059 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term469 A y s x f) = (term470 A y x f s).
Proof. exact (eq_refl (term469 A y s x f)). Qed.
Lemma lem5063060 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term468 A y s x f) = (term470 A y x f s).
Proof. exact (TRANS (@lem5063058 A y s x f) (@lem5063059 A y x f s)). Qed.
Lemma lem5063061 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term471 A y s x) = (term472 A y x s).
Proof. exact (fun_ext (fun f : A -> A => @lem5063060 A y x f s)). Qed.
Lemma lem5063062 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5063063 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term473 A y s x) = (term474 A y x s).
Proof. exact (MK_COMB (@lem5063062 A) (@lem5063061 A y x s)). Qed.
Lemma lem5063064 {A : Type'} (y : A) (s : A -> Prop) : (term475 A y s) = (term476 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem5063063 A y x s)). Qed.
Lemma lem5063065 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem5063066 {A : Type'} (y : A) (s : A -> Prop) : (term458 A y s) = (term477 A y s).
Proof. exact (MK_COMB (@lem5063065 A) (@lem5063064 A y s)). Qed.
Lemma lem5063067 {A : Type'} (y : A) (s : A -> Prop) : ((term457 A y s) = (term458 A y s)) = ((term452 A y s) = (term477 A y s)).
Proof. exact (MK_COMB (@lem5063055 A y s) (@lem5063066 A y s)). Qed.
Lemma lem5063068 {A : Type'} (y : A) (s : A -> Prop) : (term452 A y s) = (term477 A y s).
Proof. exact (EQ_MP (@lem5063067 A y s) (@lem5063042 A y s)). Qed.
Lemma lem5063069 {A : Type'} (y : A) (s : A -> Prop) : (term391 A y s) = (term477 A y s).
Proof. exact (TRANS (@lem5063038 A y s) (@lem5063068 A y s)). Qed.
Lemma lem5063070 {A : Type'} (y : A) : (term400 A y) = (term478 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063069 A y s)). Qed.
Lemma lem5063071 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063072 {A : Type'} (y : A) : (term415 A y) = (term479 A y).
Proof. exact (MK_COMB (@lem5063071 A) (@lem5063070 A y)). Qed.
Lemma lem5063074 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5063075 {A : Type'} (P : type587 A) : (term480 A P) = (term481 A P).
Proof. exact (@lem5063074 (A -> Prop) (type487 A) P). Qed.
Lemma lem5063076 {A : Type'} (y : A) : (term482 A y) = (term483 A y).
Proof. exact (@lem5063075 A (term484 A y)). Qed.
Lemma lem5063077 {A : Type'} (y : A) (s : A -> Prop) : (term485 A y s) = (term476 A y s).
Proof. exact (eq_refl (term485 A y s)). Qed.
Lemma lem5063078 {A : Type'} (x : type487 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5063079 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) : (term486 A y s x) = (term487 A y s x).
Proof. exact (MK_COMB (@lem5063077 A y s) (@lem5063078 A x)). Qed.
Lemma lem5063080 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term487 A y s x) = (term474 A y x s).
Proof. exact (eq_refl (term487 A y s x)). Qed.
Lemma lem5063081 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term486 A y s x) = (term474 A y x s).
Proof. exact (TRANS (@lem5063079 A y s x) (@lem5063080 A y x s)). Qed.
Lemma lem5063082 {A : Type'} (y : A) (s : A -> Prop) : (term488 A y s) = (term476 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem5063081 A y x s)). Qed.
Lemma lem5063083 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem5063084 {A : Type'} (y : A) (s : A -> Prop) : (term489 A y s) = (term477 A y s).
Proof. exact (MK_COMB (@lem5063083 A) (@lem5063082 A y s)). Qed.
Lemma lem5063085 {A : Type'} (y : A) : (term490 A y) = (term478 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063084 A y s)). Qed.
Lemma lem5063086 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063087 {A : Type'} (y : A) : (term482 A y) = (term479 A y).
Proof. exact (MK_COMB (@lem5063086 A) (@lem5063085 A y)). Qed.
Lemma lem5063088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063089 {A : Type'} (y : A) : (term491 A y) = (term492 A y).
Proof. exact (MK_COMB (@lem5063088) (@lem5063087 A y)). Qed.
Lemma lem5063090 {A : Type'} (y : A) (s : A -> Prop) : (term485 A y s) = (term476 A y s).
Proof. exact (eq_refl (term485 A y s)). Qed.
Lemma lem5063091 {A : Type'} (x : type623 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5063092 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term493 A y x s) = (term494 A y x s).
Proof. exact (MK_COMB (@lem5063090 A y s) (@lem5063091 A x s)). Qed.
Lemma lem5063093 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term494 A y x s) = (term495 A y x s).
Proof. exact (eq_refl (term494 A y x s)). Qed.
Lemma lem5063094 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term493 A y x s) = (term495 A y x s).
Proof. exact (TRANS (@lem5063092 A y x s) (@lem5063093 A y x s)). Qed.
Lemma lem5063095 {A : Type'} (y : A) (x : type623 A) : (term496 A y x) = (term497 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063094 A y x s)). Qed.
Lemma lem5063096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063097 {A : Type'} (y : A) (x : type623 A) : (term498 A y x) = (term499 A y x).
Proof. exact (MK_COMB (@lem5063096 A) (@lem5063095 A y x)). Qed.
Lemma lem5063098 {A : Type'} (y : A) : (term500 A y) = (term501 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem5063097 A y x)). Qed.
Lemma lem5063099 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5063100 {A : Type'} (y : A) : (term483 A y) = (term502 A y).
Proof. exact (MK_COMB (@lem5063099 A) (@lem5063098 A y)). Qed.
Lemma lem5063101 {A : Type'} (y : A) : ((term482 A y) = (term483 A y)) = ((term479 A y) = (term502 A y)).
Proof. exact (MK_COMB (@lem5063089 A y) (@lem5063100 A y)). Qed.
Lemma lem5063102 {A : Type'} (y : A) : (term479 A y) = (term502 A y).
Proof. exact (EQ_MP (@lem5063101 A y) (@lem5063076 A y)). Qed.
Lemma lem5063103 {A : Type'} (y : A) : (term415 A y) = (term502 A y).
Proof. exact (TRANS (@lem5063072 A y) (@lem5063102 A y)). Qed.
Lemma lem5063104 {A : Type'} : (term422 A) = (term503 A).
Proof. exact (fun_ext (fun y : A => @lem5063103 A y)). Qed.
Lemma lem5063105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5063106 {A : Type'} : (term437 A) = (term504 A).
Proof. exact (MK_COMB (@lem5063105 A) (@lem5063104 A)). Qed.
Lemma lem5063108 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5063109 {A : Type'} (P : type1356 A) : (term505 A P) = (term506 A P).
Proof. exact (@lem5063108 A (type623 A) P). Qed.
Lemma lem5063110 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (@lem5063109 A (term509 A)). Qed.
Lemma lem5063111 {A : Type'} (y : A) : (term510 A y) = (term501 A y).
Proof. exact (eq_refl (term510 A y)). Qed.
Lemma lem5063112 {A : Type'} (x : type623 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5063113 {A : Type'} (y : A) (x : type623 A) : (term511 A y x) = (term512 A y x).
Proof. exact (MK_COMB (@lem5063111 A y) (@lem5063112 A x)). Qed.
Lemma lem5063114 {A : Type'} (y : A) (x : type623 A) : (term512 A y x) = (term499 A y x).
Proof. exact (eq_refl (term512 A y x)). Qed.
Lemma lem5063115 {A : Type'} (y : A) (x : type623 A) : (term511 A y x) = (term499 A y x).
Proof. exact (TRANS (@lem5063113 A y x) (@lem5063114 A y x)). Qed.
Lemma lem5063116 {A : Type'} (y : A) : (term513 A y) = (term501 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem5063115 A y x)). Qed.
Lemma lem5063117 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5063118 {A : Type'} (y : A) : (term514 A y) = (term502 A y).
Proof. exact (MK_COMB (@lem5063117 A) (@lem5063116 A y)). Qed.
Lemma lem5063119 {A : Type'} : (term515 A) = (term503 A).
Proof. exact (fun_ext (fun y : A => @lem5063118 A y)). Qed.
Lemma lem5063120 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5063121 {A : Type'} : (term507 A) = (term504 A).
Proof. exact (MK_COMB (@lem5063120 A) (@lem5063119 A)). Qed.
Lemma lem5063122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063123 {A : Type'} : (term516 A) = (term517 A).
Proof. exact (MK_COMB (@lem5063122) (@lem5063121 A)). Qed.
Lemma lem5063124 {A : Type'} (y : A) : (term510 A y) = (term501 A y).
Proof. exact (eq_refl (term510 A y)). Qed.
Lemma lem5063125 {A : Type'} (x : type1361 A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5063126 {A : Type'} (x : type1361 A) (y : A) : (term518 A x y) = (term519 A x y).
Proof. exact (MK_COMB (@lem5063124 A y) (@lem5063125 A x y)). Qed.
Lemma lem5063127 {A : Type'} (x : type1361 A) (y : A) : (term519 A x y) = (term520 A x y).
Proof. exact (eq_refl (term519 A x y)). Qed.
Lemma lem5063128 {A : Type'} (x : type1361 A) (y : A) : (term518 A x y) = (term520 A x y).
Proof. exact (TRANS (@lem5063126 A x y) (@lem5063127 A x y)). Qed.
Lemma lem5063129 {A : Type'} (x : type1361 A) : (term521 A x) = (term522 A x).
Proof. exact (fun_ext (fun y : A => @lem5063128 A x y)). Qed.
Lemma lem5063130 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5063131 {A : Type'} (x : type1361 A) : (term523 A x) = (term524 A x).
Proof. exact (MK_COMB (@lem5063130 A) (@lem5063129 A x)). Qed.
Lemma lem5063132 {A : Type'} : (term525 A) = (term526 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5063131 A x)). Qed.
Lemma lem5063133 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5063134 {A : Type'} : (term508 A) = (term527 A).
Proof. exact (MK_COMB (@lem5063133 A) (@lem5063132 A)). Qed.
Lemma lem5063135 {A : Type'} : ((term507 A) = (term508 A)) = ((term504 A) = (term527 A)).
Proof. exact (MK_COMB (@lem5063123 A) (@lem5063134 A)). Qed.
Lemma lem5063136 {A : Type'} : (term504 A) = (term527 A).
Proof. exact (EQ_MP (@lem5063135 A) (@lem5063110 A)). Qed.
Lemma lem5063137 {A : Type'} : (term437 A) = (term527 A).
Proof. exact (TRANS (@lem5063106 A) (@lem5063136 A)). Qed.
Lemma lem5063138 {A : Type'} : (term434 A) = (term434 A).
Proof. exact (eq_refl (term434 A)). Qed.
Lemma lem5063139 {A : Type'} : (term438 A) = (term528 A).
Proof. exact (MK_COMB (@lem5063138 A) (@lem5063137 A)). Qed.
Lemma lem5063141 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5063142 {A : Type'} (P : Prop) (Q : type391 A) : (term529 A P Q) = (term530 A P Q).
Proof. exact (@lem5063141 (type1361 A) P Q). Qed.
Lemma lem5063143 {A : Type'} : (term531 A) = (term532 A).
Proof. exact (@lem5063142 A (term432 A) (term526 A)). Qed.
Lemma lem5063144 {A : Type'} (x : type1361 A) : (term533 A x) = (term524 A x).
Proof. exact (eq_refl (term533 A x)). Qed.
Lemma lem5063145 {A : Type'} : (term534 A) = (term526 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5063144 A x)). Qed.
Lemma lem5063146 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5063147 {A : Type'} : (term535 A) = (term527 A).
Proof. exact (MK_COMB (@lem5063146 A) (@lem5063145 A)). Qed.
Lemma lem5063148 {A : Type'} : (term434 A) = (term434 A).
Proof. exact (eq_refl (term434 A)). Qed.
Lemma lem5063149 {A : Type'} : (term531 A) = (term528 A).
Proof. exact (MK_COMB (@lem5063148 A) (@lem5063147 A)). Qed.
Lemma lem5063150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063151 {A : Type'} : (term536 A) = (term537 A).
Proof. exact (MK_COMB (@lem5063150) (@lem5063149 A)). Qed.
Lemma lem5063152 {A : Type'} (x : type1361 A) : (term533 A x) = (term524 A x).
Proof. exact (eq_refl (term533 A x)). Qed.
Lemma lem5063153 {A : Type'} : (term434 A) = (term434 A).
Proof. exact (eq_refl (term434 A)). Qed.
Lemma lem5063154 {A : Type'} (x : type1361 A) : (term538 A x) = (term539 A x).
Proof. exact (MK_COMB (@lem5063153 A) (@lem5063152 A x)). Qed.
Lemma lem5063155 {A : Type'} : (term540 A) = (term541 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5063154 A x)). Qed.
Lemma lem5063156 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5063157 {A : Type'} : (term532 A) = (term542 A).
Proof. exact (MK_COMB (@lem5063156 A) (@lem5063155 A)). Qed.
Lemma lem5063158 {A : Type'} : ((term531 A) = (term532 A)) = ((term528 A) = (term542 A)).
Proof. exact (MK_COMB (@lem5063151 A) (@lem5063157 A)). Qed.
Lemma lem5063159 {A : Type'} : (term528 A) = (term542 A).
Proof. exact (EQ_MP (@lem5063158 A) (@lem5063143 A)). Qed.
Lemma lem5063160 {A : Type'} : (term438 A) = (term542 A).
Proof. exact (TRANS (@lem5063139 A) (@lem5063159 A)). Qed.
Lemma lem5063161 {A : Type'} : (term368 A) = (term542 A).
Proof. exact (TRANS (@lem5063015 A) (@lem5063160 A)). Qed.
Lemma lem5063162 {A : Type'} : (term149 A) = (term542 A).
Proof. exact (TRANS (@lem5062318 A) (@lem5063161 A)). Qed.
Lemma lem5063163 {A : Type'} (h1 : term149 A) : term542 A.
Proof. exact (EQ_MP (@lem5063162 A) (@lem5061861 A h1)). Qed.
Lemma lem5063174 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term543 A B y f x s) = (term544 A B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem5063177 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term195 A B y f x s) = (term195 A B y f x s).
Proof. exact (eq_refl (term195 A B y f x s)). Qed.
Lemma lem5063178 {A : Type'} (P : A -> Prop) : (term345 A P) = (term346 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5063179 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term545 A B y f s) = (term546 A B y f s).
Proof. exact (@lem5063178 A (term196 A B y f s)). Qed.
Lemma lem5063180 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term547 A B y f s x) = (term195 A B y f x s).
Proof. exact (eq_refl (term547 A B y f s x)). Qed.
Lemma lem5063181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5063182 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term548 A B y f s x) = (term543 A B y f x s).
Proof. exact (MK_COMB (@lem5063181) (@lem5063180 A B y f x s)). Qed.
Lemma lem5063183 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term548 A B y f s x) = (term544 A B y f x s).
Proof. exact (TRANS (@lem5063182 A B y f x s) (@lem5063174 A B y f x s)). Qed.
Lemma lem5063184 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term549 A B y f s) = (term550 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5063183 A B y f x s)). Qed.
Lemma lem5063185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5063186 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term546 A B y f s) = (term551 A B y f s).
Proof. exact (MK_COMB (@lem5063185 A) (@lem5063184 A B y f s)). Qed.
Lemma lem5063187 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term545 A B y f s) = (term551 A B y f s).
Proof. exact (TRANS (@lem5063179 A B y f s) (@lem5063186 A B y f s)). Qed.
Lemma lem5063188 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term196 A B y f s) = (term196 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5063177 A B y f x s)). Qed.
Lemma lem5063189 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063190 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term197 A B y f s) = (term197 A B y f s).
Proof. exact (MK_COMB (@lem5063189 A) (@lem5063188 A B y f s)). Qed.
Lemma lem5063192 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term552 A B y f s) = (term552 A B y f s).
Proof. exact (eq_refl (term552 A B y f s)). Qed.
Lemma lem5063193 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term553 A B y f s) = (term553 A B y f s).
Proof. exact (MK_COMB (@lem5063192 A B y f s) (@lem5063190 A B y f s)). Qed.
Lemma lem5063195 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term554 A B y f s) = (term554 A B y f s).
Proof. exact (eq_refl (term554 A B y f s)). Qed.
Lemma lem5063196 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term555 A B y f s) = (term556 A B y f s).
Proof. exact (MK_COMB (@lem5063195 A B y f s) (@lem5063187 A B y f s)). Qed.
Lemma lem5063197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063198 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term557 A B y f s) = (term558 A B y f s).
Proof. exact (MK_COMB (@lem5063197) (@lem5063196 A B y f s)). Qed.
Lemma lem5063199 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term559 A B y f s) = (term560 A B y f s).
Proof. exact (MK_COMB (@lem5063198 A B y f s) (@lem5063193 A B y f s)). Qed.
Lemma lem5063200 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term199 A B y f s) = (term197 A B y f s)) = (term559 A B y f s).
Proof. exact (@lem17784 (term199 A B y f s) (term197 A B y f s)). Qed.
Lemma lem5063201 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term199 A B y f s) = (term197 A B y f s)) = (term560 A B y f s).
Proof. exact (TRANS (@lem5063200 A B y f s) (@lem5063199 A B y f s)). Qed.
Lemma lem5063202 {A B : Type'} (y : B) (s : A -> Prop) : (term200 A B y s) = (term561 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063201 A B y f s)). Qed.
Lemma lem5063203 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063204 {A B : Type'} (y : B) (s : A -> Prop) : (term201 A B y s) = (term562 A B y s).
Proof. exact (MK_COMB (@lem5063203 A B) (@lem5063202 A B y s)). Qed.
Lemma lem5063205 {A B : Type'} (y : B) : (term202 A B y) = (term563 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063204 A B y s)). Qed.
Lemma lem5063206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063207 {A B : Type'} (y : B) : (term203 A B y) = (term564 A B y).
Proof. exact (MK_COMB (@lem5063206 A) (@lem5063205 A B y)). Qed.
Lemma lem5063208 {A B : Type'} : (term204 A B) = (term565 A B).
Proof. exact (fun_ext (fun y : B => @lem5063207 A B y)). Qed.
Lemma lem5063209 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063210 {A B : Type'} : (term150 A B) = (term566 A B).
Proof. exact (MK_COMB (@lem5063209 B) (@lem5063208 A B)). Qed.
Lemma lem5063220 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5063221 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term567 A B P Q) = (term568 A B P Q).
Proof. exact (@lem5063220 (A -> B) P Q). Qed.
Lemma lem5063222 {A B : Type'} (y : B) (s : A -> Prop) : (term569 A B y s) = (term570 A B y s).
Proof. exact (@lem5063221 A B (term571 A B y s) (term572 A B y s)). Qed.
Lemma lem5063223 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term573 A B y s f) = (term556 A B y f s).
Proof. exact (eq_refl (term573 A B y s f)). Qed.
Lemma lem5063224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063225 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term574 A B y s f) = (term558 A B y f s).
Proof. exact (MK_COMB (@lem5063224) (@lem5063223 A B y f s)). Qed.
Lemma lem5063226 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term575 A B y s f) = (term553 A B y f s).
Proof. exact (eq_refl (term575 A B y s f)). Qed.
Lemma lem5063227 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term576 A B y s f) = (term560 A B y f s).
Proof. exact (MK_COMB (@lem5063225 A B y f s) (@lem5063226 A B y f s)). Qed.
Lemma lem5063228 {A B : Type'} (y : B) (s : A -> Prop) : (term577 A B y s) = (term561 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063227 A B y f s)). Qed.
Lemma lem5063229 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063230 {A B : Type'} (y : B) (s : A -> Prop) : (term569 A B y s) = (term562 A B y s).
Proof. exact (MK_COMB (@lem5063229 A B) (@lem5063228 A B y s)). Qed.
Lemma lem5063231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063232 {A B : Type'} (y : B) (s : A -> Prop) : (term578 A B y s) = (term579 A B y s).
Proof. exact (MK_COMB (@lem5063231) (@lem5063230 A B y s)). Qed.
Lemma lem5063233 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term573 A B y s f) = (term556 A B y f s).
Proof. exact (eq_refl (term573 A B y s f)). Qed.
Lemma lem5063234 {A B : Type'} (y : B) (s : A -> Prop) : (term580 A B y s) = (term571 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063233 A B y f s)). Qed.
Lemma lem5063235 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063236 {A B : Type'} (y : B) (s : A -> Prop) : (term581 A B y s) = (term582 A B y s).
Proof. exact (MK_COMB (@lem5063235 A B) (@lem5063234 A B y s)). Qed.
Lemma lem5063237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063238 {A B : Type'} (y : B) (s : A -> Prop) : (term583 A B y s) = (term584 A B y s).
Proof. exact (MK_COMB (@lem5063237) (@lem5063236 A B y s)). Qed.
Lemma lem5063239 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term575 A B y s f) = (term553 A B y f s).
Proof. exact (eq_refl (term575 A B y s f)). Qed.
Lemma lem5063240 {A B : Type'} (y : B) (s : A -> Prop) : (term585 A B y s) = (term572 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063239 A B y f s)). Qed.
Lemma lem5063241 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063242 {A B : Type'} (y : B) (s : A -> Prop) : (term586 A B y s) = (term587 A B y s).
Proof. exact (MK_COMB (@lem5063241 A B) (@lem5063240 A B y s)). Qed.
Lemma lem5063243 {A B : Type'} (y : B) (s : A -> Prop) : (term570 A B y s) = (term588 A B y s).
Proof. exact (MK_COMB (@lem5063238 A B y s) (@lem5063242 A B y s)). Qed.
Lemma lem5063244 {A B : Type'} (y : B) (s : A -> Prop) : ((term569 A B y s) = (term570 A B y s)) = ((term562 A B y s) = (term588 A B y s)).
Proof. exact (MK_COMB (@lem5063232 A B y s) (@lem5063243 A B y s)). Qed.
Lemma lem5063245 {A B : Type'} (y : B) (s : A -> Prop) : (term562 A B y s) = (term588 A B y s).
Proof. exact (EQ_MP (@lem5063244 A B y s) (@lem5063222 A B y s)). Qed.
Lemma lem5063438 {A B : Type'} (y : B) : (term563 A B y) = (term589 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063245 A B y s)). Qed.
Lemma lem5063439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063440 {A B : Type'} (y : B) : (term564 A B y) = (term590 A B y).
Proof. exact (MK_COMB (@lem5063439 A) (@lem5063438 A B y)). Qed.
Lemma lem5063442 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5063443 {A : Type'} (P : type686 A) (Q : type686 A) : (term395 A P Q) = (term396 A P Q).
Proof. exact (@lem5063442 (A -> Prop) P Q). Qed.
Lemma lem5063444 {A B : Type'} (y : B) : (term591 A B y) = (term592 A B y).
Proof. exact (@lem5063443 A (term593 A B y) (term594 A B y)). Qed.
Lemma lem5063445 {A B : Type'} (y : B) (s : A -> Prop) : (term595 A B y s) = (term582 A B y s).
Proof. exact (eq_refl (term595 A B y s)). Qed.
Lemma lem5063446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063447 {A B : Type'} (y : B) (s : A -> Prop) : (term596 A B y s) = (term584 A B y s).
Proof. exact (MK_COMB (@lem5063446) (@lem5063445 A B y s)). Qed.
Lemma lem5063448 {A B : Type'} (y : B) (s : A -> Prop) : (term597 A B y s) = (term587 A B y s).
Proof. exact (eq_refl (term597 A B y s)). Qed.
Lemma lem5063449 {A B : Type'} (y : B) (s : A -> Prop) : (term598 A B y s) = (term588 A B y s).
Proof. exact (MK_COMB (@lem5063447 A B y s) (@lem5063448 A B y s)). Qed.
Lemma lem5063450 {A B : Type'} (y : B) : (term599 A B y) = (term589 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063449 A B y s)). Qed.
Lemma lem5063451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063452 {A B : Type'} (y : B) : (term591 A B y) = (term590 A B y).
Proof. exact (MK_COMB (@lem5063451 A) (@lem5063450 A B y)). Qed.
Lemma lem5063453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063454 {A B : Type'} (y : B) : (term600 A B y) = (term601 A B y).
Proof. exact (MK_COMB (@lem5063453) (@lem5063452 A B y)). Qed.
Lemma lem5063455 {A B : Type'} (y : B) (s : A -> Prop) : (term595 A B y s) = (term582 A B y s).
Proof. exact (eq_refl (term595 A B y s)). Qed.
Lemma lem5063456 {A B : Type'} (y : B) : (term602 A B y) = (term593 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063455 A B y s)). Qed.
Lemma lem5063457 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063458 {A B : Type'} (y : B) : (term603 A B y) = (term604 A B y).
Proof. exact (MK_COMB (@lem5063457 A) (@lem5063456 A B y)). Qed.
Lemma lem5063459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063460 {A B : Type'} (y : B) : (term605 A B y) = (term606 A B y).
Proof. exact (MK_COMB (@lem5063459) (@lem5063458 A B y)). Qed.
Lemma lem5063461 {A B : Type'} (y : B) (s : A -> Prop) : (term597 A B y s) = (term587 A B y s).
Proof. exact (eq_refl (term597 A B y s)). Qed.
Lemma lem5063462 {A B : Type'} (y : B) : (term607 A B y) = (term594 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063461 A B y s)). Qed.
Lemma lem5063463 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063464 {A B : Type'} (y : B) : (term608 A B y) = (term609 A B y).
Proof. exact (MK_COMB (@lem5063463 A) (@lem5063462 A B y)). Qed.
Lemma lem5063465 {A B : Type'} (y : B) : (term592 A B y) = (term610 A B y).
Proof. exact (MK_COMB (@lem5063460 A B y) (@lem5063464 A B y)). Qed.
Lemma lem5063466 {A B : Type'} (y : B) : ((term591 A B y) = (term592 A B y)) = ((term590 A B y) = (term610 A B y)).
Proof. exact (MK_COMB (@lem5063454 A B y) (@lem5063465 A B y)). Qed.
Lemma lem5063467 {A B : Type'} (y : B) : (term590 A B y) = (term610 A B y).
Proof. exact (EQ_MP (@lem5063466 A B y) (@lem5063444 A B y)). Qed.
Lemma lem5063668 {A B : Type'} (y : B) : (term564 A B y) = (term610 A B y).
Proof. exact (TRANS (@lem5063440 A B y) (@lem5063467 A B y)). Qed.
Lemma lem5063669 {A B : Type'} : (term565 A B) = (term611 A B).
Proof. exact (fun_ext (fun y : B => @lem5063668 A B y)). Qed.
Lemma lem5063670 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063671 {A B : Type'} : (term566 A B) = (term612 A B).
Proof. exact (MK_COMB (@lem5063670 B) (@lem5063669 A B)). Qed.
Lemma lem5063673 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5063674 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term369 B P Q) = (term370 B P Q).
Proof. exact (@lem5063673 B P Q). Qed.
Lemma lem5063675 {A B : Type'} : (term613 A B) = (term614 A B).
Proof. exact (@lem5063674 B (term615 A B) (term616 A B)). Qed.
Lemma lem5063676 {A B : Type'} (y : B) : (term617 A B y) = (term604 A B y).
Proof. exact (eq_refl (term617 A B y)). Qed.
Lemma lem5063677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063678 {A B : Type'} (y : B) : (term618 A B y) = (term606 A B y).
Proof. exact (MK_COMB (@lem5063677) (@lem5063676 A B y)). Qed.
Lemma lem5063679 {A B : Type'} (y : B) : (term619 A B y) = (term609 A B y).
Proof. exact (eq_refl (term619 A B y)). Qed.
Lemma lem5063680 {A B : Type'} (y : B) : (term620 A B y) = (term610 A B y).
Proof. exact (MK_COMB (@lem5063678 A B y) (@lem5063679 A B y)). Qed.
Lemma lem5063681 {A B : Type'} : (term621 A B) = (term611 A B).
Proof. exact (fun_ext (fun y : B => @lem5063680 A B y)). Qed.
Lemma lem5063682 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063683 {A B : Type'} : (term613 A B) = (term612 A B).
Proof. exact (MK_COMB (@lem5063682 B) (@lem5063681 A B)). Qed.
Lemma lem5063684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063685 {A B : Type'} : (term622 A B) = (term623 A B).
Proof. exact (MK_COMB (@lem5063684) (@lem5063683 A B)). Qed.
Lemma lem5063686 {A B : Type'} (y : B) : (term617 A B y) = (term604 A B y).
Proof. exact (eq_refl (term617 A B y)). Qed.
Lemma lem5063687 {A B : Type'} : (term624 A B) = (term615 A B).
Proof. exact (fun_ext (fun y : B => @lem5063686 A B y)). Qed.
Lemma lem5063688 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063689 {A B : Type'} : (term625 A B) = (term626 A B).
Proof. exact (MK_COMB (@lem5063688 B) (@lem5063687 A B)). Qed.
Lemma lem5063690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5063691 {A B : Type'} : (term627 A B) = (term628 A B).
Proof. exact (MK_COMB (@lem5063690) (@lem5063689 A B)). Qed.
Lemma lem5063692 {A B : Type'} (y : B) : (term619 A B y) = (term609 A B y).
Proof. exact (eq_refl (term619 A B y)). Qed.
Lemma lem5063693 {A B : Type'} : (term629 A B) = (term616 A B).
Proof. exact (fun_ext (fun y : B => @lem5063692 A B y)). Qed.
Lemma lem5063694 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063695 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (MK_COMB (@lem5063694 B) (@lem5063693 A B)). Qed.
Lemma lem5063696 {A B : Type'} : (term614 A B) = (term632 A B).
Proof. exact (MK_COMB (@lem5063691 A B) (@lem5063695 A B)). Qed.
Lemma lem5063697 {A B : Type'} : ((term613 A B) = (term614 A B)) = ((term612 A B) = (term632 A B)).
Proof. exact (MK_COMB (@lem5063685 A B) (@lem5063696 A B)). Qed.
Lemma lem5063698 {A B : Type'} : (term612 A B) = (term632 A B).
Proof. exact (EQ_MP (@lem5063697 A B) (@lem5063675 A B)). Qed.
Lemma lem5063907 {A B : Type'} : (term566 A B) = (term632 A B).
Proof. exact (TRANS (@lem5063671 A B) (@lem5063698 A B)). Qed.
Lemma lem5063909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5063910 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem5063909 A P Q). Qed.
Lemma lem5063911 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term633 A B y f s) = (term634 A B y f s).
Proof. exact (@lem5063910 A (term635 A B y f s) (term196 A B y f s)). Qed.
Lemma lem5063912 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term547 A B y f s x) = (term195 A B y f x s).
Proof. exact (eq_refl (term547 A B y f s x)). Qed.
Lemma lem5063913 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term636 A B y f s) = (term196 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5063912 A B y f x s)). Qed.
Lemma lem5063914 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063915 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term637 A B y f s) = (term197 A B y f s).
Proof. exact (MK_COMB (@lem5063914 A) (@lem5063913 A B y f s)). Qed.
Lemma lem5063916 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term552 A B y f s) = (term552 A B y f s).
Proof. exact (eq_refl (term552 A B y f s)). Qed.
Lemma lem5063917 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term633 A B y f s) = (term553 A B y f s).
Proof. exact (MK_COMB (@lem5063916 A B y f s) (@lem5063915 A B y f s)). Qed.
Lemma lem5063918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063919 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term638 A B y f s) = (term639 A B y f s).
Proof. exact (MK_COMB (@lem5063918) (@lem5063917 A B y f s)). Qed.
Lemma lem5063920 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term547 A B y f s x) = (term195 A B y f x s).
Proof. exact (eq_refl (term547 A B y f s x)). Qed.
Lemma lem5063921 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term552 A B y f s) = (term552 A B y f s).
Proof. exact (eq_refl (term552 A B y f s)). Qed.
Lemma lem5063922 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term640 A B y f s x) = (term641 A B y f x s).
Proof. exact (MK_COMB (@lem5063921 A B y f s) (@lem5063920 A B y f x s)). Qed.
Lemma lem5063923 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term642 A B y f s) = (term643 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5063922 A B y f x s)). Qed.
Lemma lem5063924 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063925 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term634 A B y f s) = (term644 A B y f s).
Proof. exact (MK_COMB (@lem5063924 A) (@lem5063923 A B y f s)). Qed.
Lemma lem5063926 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term633 A B y f s) = (term634 A B y f s)) = ((term553 A B y f s) = (term644 A B y f s)).
Proof. exact (MK_COMB (@lem5063919 A B y f s) (@lem5063925 A B y f s)). Qed.
Lemma lem5063927 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term553 A B y f s) = (term644 A B y f s).
Proof. exact (EQ_MP (@lem5063926 A B y f s) (@lem5063911 A B y f s)). Qed.
Lemma lem5063928 {A B : Type'} (y : B) (s : A -> Prop) : (term572 A B y s) = (term645 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063927 A B y f s)). Qed.
Lemma lem5063929 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063930 {A B : Type'} (y : B) (s : A -> Prop) : (term587 A B y s) = (term646 A B y s).
Proof. exact (MK_COMB (@lem5063929 A B) (@lem5063928 A B y s)). Qed.
Lemma lem5063932 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5063933 {A B : Type'} (P : type551 A B) : (term647 A B P) = (term648 A B P).
Proof. exact (@lem5063932 (A -> B) A P). Qed.
Lemma lem5063934 {A B : Type'} (y : B) (s : A -> Prop) : (term649 A B y s) = (term650 A B y s).
Proof. exact (@lem5063933 A B (term651 A B y s)). Qed.
Lemma lem5063935 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term652 A B y s f) = (term643 A B y f s).
Proof. exact (eq_refl (term652 A B y s f)). Qed.
Lemma lem5063936 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5063937 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term653 A B y s f x) = (term654 A B y f s x).
Proof. exact (MK_COMB (@lem5063935 A B y f s) (@lem5063936 A x)). Qed.
Lemma lem5063938 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term654 A B y f s x) = (term641 A B y f x s).
Proof. exact (eq_refl (term654 A B y f s x)). Qed.
Lemma lem5063939 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term653 A B y s f x) = (term641 A B y f x s).
Proof. exact (TRANS (@lem5063937 A B y f s x) (@lem5063938 A B y f x s)). Qed.
Lemma lem5063940 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term655 A B y s f) = (term643 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5063939 A B y f x s)). Qed.
Lemma lem5063941 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5063942 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term656 A B y s f) = (term644 A B y f s).
Proof. exact (MK_COMB (@lem5063941 A) (@lem5063940 A B y f s)). Qed.
Lemma lem5063943 {A B : Type'} (y : B) (s : A -> Prop) : (term657 A B y s) = (term645 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063942 A B y f s)). Qed.
Lemma lem5063944 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063945 {A B : Type'} (y : B) (s : A -> Prop) : (term649 A B y s) = (term646 A B y s).
Proof. exact (MK_COMB (@lem5063944 A B) (@lem5063943 A B y s)). Qed.
Lemma lem5063946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063947 {A B : Type'} (y : B) (s : A -> Prop) : (term658 A B y s) = (term659 A B y s).
Proof. exact (MK_COMB (@lem5063946) (@lem5063945 A B y s)). Qed.
Lemma lem5063948 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term652 A B y s f) = (term643 A B y f s).
Proof. exact (eq_refl (term652 A B y s f)). Qed.
Lemma lem5063949 {A B : Type'} (x : type569 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5063950 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) (f : A -> B) : (term660 A B y s x f) = (term661 A B y s x f).
Proof. exact (MK_COMB (@lem5063948 A B y f s) (@lem5063949 A B x f)). Qed.
Lemma lem5063951 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term661 A B y s x f) = (term662 A B y x f s).
Proof. exact (eq_refl (term661 A B y s x f)). Qed.
Lemma lem5063952 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term660 A B y s x f) = (term662 A B y x f s).
Proof. exact (TRANS (@lem5063950 A B y s x f) (@lem5063951 A B y x f s)). Qed.
Lemma lem5063953 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term663 A B y s x) = (term664 A B y x s).
Proof. exact (fun_ext (fun f : A -> B => @lem5063952 A B y x f s)). Qed.
Lemma lem5063954 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5063955 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term665 A B y s x) = (term666 A B y x s).
Proof. exact (MK_COMB (@lem5063954 A B) (@lem5063953 A B y x s)). Qed.
Lemma lem5063956 {A B : Type'} (y : B) (s : A -> Prop) : (term667 A B y s) = (term668 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem5063955 A B y x s)). Qed.
Lemma lem5063957 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem5063958 {A B : Type'} (y : B) (s : A -> Prop) : (term650 A B y s) = (term669 A B y s).
Proof. exact (MK_COMB (@lem5063957 A B) (@lem5063956 A B y s)). Qed.
Lemma lem5063959 {A B : Type'} (y : B) (s : A -> Prop) : ((term649 A B y s) = (term650 A B y s)) = ((term646 A B y s) = (term669 A B y s)).
Proof. exact (MK_COMB (@lem5063947 A B y s) (@lem5063958 A B y s)). Qed.
Lemma lem5063960 {A B : Type'} (y : B) (s : A -> Prop) : (term646 A B y s) = (term669 A B y s).
Proof. exact (EQ_MP (@lem5063959 A B y s) (@lem5063934 A B y s)). Qed.
Lemma lem5063961 {A B : Type'} (y : B) (s : A -> Prop) : (term587 A B y s) = (term669 A B y s).
Proof. exact (TRANS (@lem5063930 A B y s) (@lem5063960 A B y s)). Qed.
Lemma lem5063962 {A B : Type'} (y : B) : (term594 A B y) = (term670 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063961 A B y s)). Qed.
Lemma lem5063963 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063964 {A B : Type'} (y : B) : (term609 A B y) = (term671 A B y).
Proof. exact (MK_COMB (@lem5063963 A) (@lem5063962 A B y)). Qed.
Lemma lem5063966 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5063967 {A B : Type'} (P : type593 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (@lem5063966 (A -> Prop) (type569 A B) P). Qed.
Lemma lem5063968 {A B : Type'} (y : B) : (term674 A B y) = (term675 A B y).
Proof. exact (@lem5063967 A B (term676 A B y)). Qed.
Lemma lem5063969 {A B : Type'} (y : B) (s : A -> Prop) : (term677 A B y s) = (term668 A B y s).
Proof. exact (eq_refl (term677 A B y s)). Qed.
Lemma lem5063970 {A B : Type'} (x : type569 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5063971 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) : (term678 A B y s x) = (term679 A B y s x).
Proof. exact (MK_COMB (@lem5063969 A B y s) (@lem5063970 A B x)). Qed.
Lemma lem5063972 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term679 A B y s x) = (term666 A B y x s).
Proof. exact (eq_refl (term679 A B y s x)). Qed.
Lemma lem5063973 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term678 A B y s x) = (term666 A B y x s).
Proof. exact (TRANS (@lem5063971 A B y s x) (@lem5063972 A B y x s)). Qed.
Lemma lem5063974 {A B : Type'} (y : B) (s : A -> Prop) : (term680 A B y s) = (term668 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem5063973 A B y x s)). Qed.
Lemma lem5063975 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem5063976 {A B : Type'} (y : B) (s : A -> Prop) : (term681 A B y s) = (term669 A B y s).
Proof. exact (MK_COMB (@lem5063975 A B) (@lem5063974 A B y s)). Qed.
Lemma lem5063977 {A B : Type'} (y : B) : (term682 A B y) = (term670 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063976 A B y s)). Qed.
Lemma lem5063978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063979 {A B : Type'} (y : B) : (term674 A B y) = (term671 A B y).
Proof. exact (MK_COMB (@lem5063978 A) (@lem5063977 A B y)). Qed.
Lemma lem5063980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5063981 {A B : Type'} (y : B) : (term683 A B y) = (term684 A B y).
Proof. exact (MK_COMB (@lem5063980) (@lem5063979 A B y)). Qed.
Lemma lem5063982 {A B : Type'} (y : B) (s : A -> Prop) : (term677 A B y s) = (term668 A B y s).
Proof. exact (eq_refl (term677 A B y s)). Qed.
Lemma lem5063983 {A B : Type'} (x : type631 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5063984 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term685 A B y x s) = (term686 A B y x s).
Proof. exact (MK_COMB (@lem5063982 A B y s) (@lem5063983 A B x s)). Qed.
Lemma lem5063985 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term686 A B y x s) = (term687 A B y x s).
Proof. exact (eq_refl (term686 A B y x s)). Qed.
Lemma lem5063986 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term685 A B y x s) = (term687 A B y x s).
Proof. exact (TRANS (@lem5063984 A B y x s) (@lem5063985 A B y x s)). Qed.
Lemma lem5063987 {A B : Type'} (y : B) (x : type631 A B) : (term688 A B y x) = (term689 A B y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5063986 A B y x s)). Qed.
Lemma lem5063988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5063989 {A B : Type'} (y : B) (x : type631 A B) : (term690 A B y x) = (term691 A B y x).
Proof. exact (MK_COMB (@lem5063988 A) (@lem5063987 A B y x)). Qed.
Lemma lem5063990 {A B : Type'} (y : B) : (term692 A B y) = (term693 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem5063989 A B y x)). Qed.
Lemma lem5063991 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5063992 {A B : Type'} (y : B) : (term675 A B y) = (term694 A B y).
Proof. exact (MK_COMB (@lem5063991 A B) (@lem5063990 A B y)). Qed.
Lemma lem5063993 {A B : Type'} (y : B) : ((term674 A B y) = (term675 A B y)) = ((term671 A B y) = (term694 A B y)).
Proof. exact (MK_COMB (@lem5063981 A B y) (@lem5063992 A B y)). Qed.
Lemma lem5063994 {A B : Type'} (y : B) : (term671 A B y) = (term694 A B y).
Proof. exact (EQ_MP (@lem5063993 A B y) (@lem5063968 A B y)). Qed.
Lemma lem5063995 {A B : Type'} (y : B) : (term609 A B y) = (term694 A B y).
Proof. exact (TRANS (@lem5063964 A B y) (@lem5063994 A B y)). Qed.
Lemma lem5063996 {A B : Type'} : (term616 A B) = (term695 A B).
Proof. exact (fun_ext (fun y : B => @lem5063995 A B y)). Qed.
Lemma lem5063997 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5063998 {A B : Type'} : (term631 A B) = (term696 A B).
Proof. exact (MK_COMB (@lem5063997 B) (@lem5063996 A B)). Qed.
Lemma lem5064000 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5064001 {A B : Type'} (P : type1437 A B) : (term697 A B P) = (term698 A B P).
Proof. exact (@lem5064000 B (type631 A B) P). Qed.
Lemma lem5064002 {A B : Type'} : (term699 A B) = (term700 A B).
Proof. exact (@lem5064001 A B (term701 A B)). Qed.
Lemma lem5064003 {A B : Type'} (y : B) : (term702 A B y) = (term693 A B y).
Proof. exact (eq_refl (term702 A B y)). Qed.
Lemma lem5064004 {A B : Type'} (x : type631 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5064005 {A B : Type'} (y : B) (x : type631 A B) : (term703 A B y x) = (term704 A B y x).
Proof. exact (MK_COMB (@lem5064003 A B y) (@lem5064004 A B x)). Qed.
Lemma lem5064006 {A B : Type'} (y : B) (x : type631 A B) : (term704 A B y x) = (term691 A B y x).
Proof. exact (eq_refl (term704 A B y x)). Qed.
Lemma lem5064007 {A B : Type'} (y : B) (x : type631 A B) : (term703 A B y x) = (term691 A B y x).
Proof. exact (TRANS (@lem5064005 A B y x) (@lem5064006 A B y x)). Qed.
Lemma lem5064008 {A B : Type'} (y : B) : (term705 A B y) = (term693 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem5064007 A B y x)). Qed.
Lemma lem5064009 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5064010 {A B : Type'} (y : B) : (term706 A B y) = (term694 A B y).
Proof. exact (MK_COMB (@lem5064009 A B) (@lem5064008 A B y)). Qed.
Lemma lem5064011 {A B : Type'} : (term707 A B) = (term695 A B).
Proof. exact (fun_ext (fun y : B => @lem5064010 A B y)). Qed.
Lemma lem5064012 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064013 {A B : Type'} : (term699 A B) = (term696 A B).
Proof. exact (MK_COMB (@lem5064012 B) (@lem5064011 A B)). Qed.
Lemma lem5064014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064015 {A B : Type'} : (term708 A B) = (term709 A B).
Proof. exact (MK_COMB (@lem5064014) (@lem5064013 A B)). Qed.
Lemma lem5064016 {A B : Type'} (y : B) : (term702 A B y) = (term693 A B y).
Proof. exact (eq_refl (term702 A B y)). Qed.
Lemma lem5064017 {A B : Type'} (x : type1448 A B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5064018 {A B : Type'} (x : type1448 A B) (y : B) : (term710 A B x y) = (term711 A B x y).
Proof. exact (MK_COMB (@lem5064016 A B y) (@lem5064017 A B x y)). Qed.
Lemma lem5064019 {A B : Type'} (x : type1448 A B) (y : B) : (term711 A B x y) = (term712 A B x y).
Proof. exact (eq_refl (term711 A B x y)). Qed.
Lemma lem5064020 {A B : Type'} (x : type1448 A B) (y : B) : (term710 A B x y) = (term712 A B x y).
Proof. exact (TRANS (@lem5064018 A B x y) (@lem5064019 A B x y)). Qed.
Lemma lem5064021 {A B : Type'} (x : type1448 A B) : (term713 A B x) = (term714 A B x).
Proof. exact (fun_ext (fun y : B => @lem5064020 A B x y)). Qed.
Lemma lem5064022 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064023 {A B : Type'} (x : type1448 A B) : (term715 A B x) = (term716 A B x).
Proof. exact (MK_COMB (@lem5064022 B) (@lem5064021 A B x)). Qed.
Lemma lem5064024 {A B : Type'} : (term717 A B) = (term718 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5064023 A B x)). Qed.
Lemma lem5064025 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5064026 {A B : Type'} : (term700 A B) = (term719 A B).
Proof. exact (MK_COMB (@lem5064025 A B) (@lem5064024 A B)). Qed.
Lemma lem5064027 {A B : Type'} : ((term699 A B) = (term700 A B)) = ((term696 A B) = (term719 A B)).
Proof. exact (MK_COMB (@lem5064015 A B) (@lem5064026 A B)). Qed.
Lemma lem5064028 {A B : Type'} : (term696 A B) = (term719 A B).
Proof. exact (EQ_MP (@lem5064027 A B) (@lem5064002 A B)). Qed.
Lemma lem5064029 {A B : Type'} : (term631 A B) = (term719 A B).
Proof. exact (TRANS (@lem5063998 A B) (@lem5064028 A B)). Qed.
Lemma lem5064030 {A B : Type'} : (term628 A B) = (term628 A B).
Proof. exact (eq_refl (term628 A B)). Qed.
Lemma lem5064031 {A B : Type'} : (term632 A B) = (term720 A B).
Proof. exact (MK_COMB (@lem5064030 A B) (@lem5064029 A B)). Qed.
Lemma lem5064033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5064034 {A B : Type'} (P : Prop) (Q : type719 A B) : (term721 A B P Q) = (term722 A B P Q).
Proof. exact (@lem5064033 (type1448 A B) P Q). Qed.
Lemma lem5064035 {A B : Type'} : (term723 A B) = (term724 A B).
Proof. exact (@lem5064034 A B (term626 A B) (term718 A B)). Qed.
Lemma lem5064036 {A B : Type'} (x : type1448 A B) : (term725 A B x) = (term716 A B x).
Proof. exact (eq_refl (term725 A B x)). Qed.
Lemma lem5064037 {A B : Type'} : (term726 A B) = (term718 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5064036 A B x)). Qed.
Lemma lem5064038 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5064039 {A B : Type'} : (term727 A B) = (term719 A B).
Proof. exact (MK_COMB (@lem5064038 A B) (@lem5064037 A B)). Qed.
Lemma lem5064040 {A B : Type'} : (term628 A B) = (term628 A B).
Proof. exact (eq_refl (term628 A B)). Qed.
Lemma lem5064041 {A B : Type'} : (term723 A B) = (term720 A B).
Proof. exact (MK_COMB (@lem5064040 A B) (@lem5064039 A B)). Qed.
Lemma lem5064042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064043 {A B : Type'} : (term728 A B) = (term729 A B).
Proof. exact (MK_COMB (@lem5064042) (@lem5064041 A B)). Qed.
Lemma lem5064044 {A B : Type'} (x : type1448 A B) : (term725 A B x) = (term716 A B x).
Proof. exact (eq_refl (term725 A B x)). Qed.
Lemma lem5064045 {A B : Type'} : (term628 A B) = (term628 A B).
Proof. exact (eq_refl (term628 A B)). Qed.
Lemma lem5064046 {A B : Type'} (x : type1448 A B) : (term730 A B x) = (term731 A B x).
Proof. exact (MK_COMB (@lem5064045 A B) (@lem5064044 A B x)). Qed.
Lemma lem5064047 {A B : Type'} : (term732 A B) = (term733 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5064046 A B x)). Qed.
Lemma lem5064048 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5064049 {A B : Type'} : (term724 A B) = (term734 A B).
Proof. exact (MK_COMB (@lem5064048 A B) (@lem5064047 A B)). Qed.
Lemma lem5064050 {A B : Type'} : ((term723 A B) = (term724 A B)) = ((term720 A B) = (term734 A B)).
Proof. exact (MK_COMB (@lem5064043 A B) (@lem5064049 A B)). Qed.
Lemma lem5064051 {A B : Type'} : (term720 A B) = (term734 A B).
Proof. exact (EQ_MP (@lem5064050 A B) (@lem5064035 A B)). Qed.
Lemma lem5064052 {A B : Type'} : (term632 A B) = (term734 A B).
Proof. exact (TRANS (@lem5064031 A B) (@lem5064051 A B)). Qed.
Lemma lem5064053 {A B : Type'} : (term566 A B) = (term734 A B).
Proof. exact (TRANS (@lem5063907 A B) (@lem5064052 A B)). Qed.
Lemma lem5064054 {A B : Type'} : (term150 A B) = (term734 A B).
Proof. exact (TRANS (@lem5063210 A B) (@lem5064053 A B)). Qed.
Lemma lem5064055 {A B : Type'} (h1 : term150 A B) : term734 A B.
Proof. exact (EQ_MP (@lem5064054 A B) (@lem5061862 A B h1)). Qed.
Lemma lem5064066 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term343 B y f x s) = (term344 B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN B x s)). Qed.
Lemma lem5064069 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term185 B y f x s) = (term185 B y f x s).
Proof. exact (eq_refl (term185 B y f x s)). Qed.
Lemma lem5064070 {B : Type'} (P : B -> Prop) : (term345 B P) = (term346 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem5064071 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term347 B y f s) = (term348 B y f s).
Proof. exact (@lem5064070 B (term186 B y f s)). Qed.
Lemma lem5064072 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term349 B y f s x) = (term185 B y f x s).
Proof. exact (eq_refl (term349 B y f s x)). Qed.
Lemma lem5064073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5064074 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term350 B y f s x) = (term343 B y f x s).
Proof. exact (MK_COMB (@lem5064073) (@lem5064072 B y f x s)). Qed.
Lemma lem5064075 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term350 B y f s x) = (term344 B y f x s).
Proof. exact (TRANS (@lem5064074 B y f x s) (@lem5064066 B y f x s)). Qed.
Lemma lem5064076 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term351 B y f s) = (term352 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5064075 B y f x s)). Qed.
Lemma lem5064077 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064078 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term348 B y f s) = (term353 B y f s).
Proof. exact (MK_COMB (@lem5064077 B) (@lem5064076 B y f s)). Qed.
Lemma lem5064079 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term347 B y f s) = (term353 B y f s).
Proof. exact (TRANS (@lem5064071 B y f s) (@lem5064078 B y f s)). Qed.
Lemma lem5064080 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term186 B y f s) = (term186 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5064069 B y f x s)). Qed.
Lemma lem5064081 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5064082 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term187 B y f s) = (term187 B y f s).
Proof. exact (MK_COMB (@lem5064081 B) (@lem5064080 B y f s)). Qed.
Lemma lem5064084 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term354 B y f s) = (term354 B y f s).
Proof. exact (eq_refl (term354 B y f s)). Qed.
Lemma lem5064085 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term355 B y f s) = (term355 B y f s).
Proof. exact (MK_COMB (@lem5064084 B y f s) (@lem5064082 B y f s)). Qed.
Lemma lem5064087 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term356 B y f s) = (term356 B y f s).
Proof. exact (eq_refl (term356 B y f s)). Qed.
Lemma lem5064088 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term357 B y f s) = (term358 B y f s).
Proof. exact (MK_COMB (@lem5064087 B y f s) (@lem5064079 B y f s)). Qed.
Lemma lem5064089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064090 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term359 B y f s) = (term360 B y f s).
Proof. exact (MK_COMB (@lem5064089) (@lem5064088 B y f s)). Qed.
Lemma lem5064091 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term361 B y f s) = (term362 B y f s).
Proof. exact (MK_COMB (@lem5064090 B y f s) (@lem5064085 B y f s)). Qed.
Lemma lem5064092 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term189 B y f s) = (term187 B y f s)) = (term361 B y f s).
Proof. exact (@lem17784 (term189 B y f s) (term187 B y f s)). Qed.
Lemma lem5064093 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term189 B y f s) = (term187 B y f s)) = (term362 B y f s).
Proof. exact (TRANS (@lem5064092 B y f s) (@lem5064091 B y f s)). Qed.
Lemma lem5064094 {B : Type'} (y : B) (s : B -> Prop) : (term190 B y s) = (term363 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064093 B y f s)). Qed.
Lemma lem5064095 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064096 {B : Type'} (y : B) (s : B -> Prop) : (term191 B y s) = (term364 B y s).
Proof. exact (MK_COMB (@lem5064095 B) (@lem5064094 B y s)). Qed.
Lemma lem5064097 {B : Type'} (y : B) : (term192 B y) = (term365 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064096 B y s)). Qed.
Lemma lem5064098 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064099 {B : Type'} (y : B) : (term193 B y) = (term366 B y).
Proof. exact (MK_COMB (@lem5064098 B) (@lem5064097 B y)). Qed.
Lemma lem5064100 {B : Type'} : (term194 B) = (term367 B).
Proof. exact (fun_ext (fun y : B => @lem5064099 B y)). Qed.
Lemma lem5064101 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064102 {B : Type'} : (term149 B) = (term368 B).
Proof. exact (MK_COMB (@lem5064101 B) (@lem5064100 B)). Qed.
Lemma lem5064112 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5064113 {B : Type'} (P : type488 B) (Q : type488 B) : (term371 B P Q) = (term372 B P Q).
Proof. exact (@lem5064112 (B -> B) P Q). Qed.
Lemma lem5064114 {B : Type'} (y : B) (s : B -> Prop) : (term373 B y s) = (term374 B y s).
Proof. exact (@lem5064113 B (term375 B y s) (term376 B y s)). Qed.
Lemma lem5064115 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term377 B y s f) = (term358 B y f s).
Proof. exact (eq_refl (term377 B y s f)). Qed.
Lemma lem5064116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064117 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term378 B y s f) = (term360 B y f s).
Proof. exact (MK_COMB (@lem5064116) (@lem5064115 B y f s)). Qed.
Lemma lem5064118 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term379 B y s f) = (term355 B y f s).
Proof. exact (eq_refl (term379 B y s f)). Qed.
Lemma lem5064119 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term380 B y s f) = (term362 B y f s).
Proof. exact (MK_COMB (@lem5064117 B y f s) (@lem5064118 B y f s)). Qed.
Lemma lem5064120 {B : Type'} (y : B) (s : B -> Prop) : (term381 B y s) = (term363 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064119 B y f s)). Qed.
Lemma lem5064121 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064122 {B : Type'} (y : B) (s : B -> Prop) : (term373 B y s) = (term364 B y s).
Proof. exact (MK_COMB (@lem5064121 B) (@lem5064120 B y s)). Qed.
Lemma lem5064123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064124 {B : Type'} (y : B) (s : B -> Prop) : (term382 B y s) = (term383 B y s).
Proof. exact (MK_COMB (@lem5064123) (@lem5064122 B y s)). Qed.
Lemma lem5064125 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term377 B y s f) = (term358 B y f s).
Proof. exact (eq_refl (term377 B y s f)). Qed.
Lemma lem5064126 {B : Type'} (y : B) (s : B -> Prop) : (term384 B y s) = (term375 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064125 B y f s)). Qed.
Lemma lem5064127 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064128 {B : Type'} (y : B) (s : B -> Prop) : (term385 B y s) = (term386 B y s).
Proof. exact (MK_COMB (@lem5064127 B) (@lem5064126 B y s)). Qed.
Lemma lem5064129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064130 {B : Type'} (y : B) (s : B -> Prop) : (term387 B y s) = (term388 B y s).
Proof. exact (MK_COMB (@lem5064129) (@lem5064128 B y s)). Qed.
Lemma lem5064131 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term379 B y s f) = (term355 B y f s).
Proof. exact (eq_refl (term379 B y s f)). Qed.
Lemma lem5064132 {B : Type'} (y : B) (s : B -> Prop) : (term389 B y s) = (term376 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064131 B y f s)). Qed.
Lemma lem5064133 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064134 {B : Type'} (y : B) (s : B -> Prop) : (term390 B y s) = (term391 B y s).
Proof. exact (MK_COMB (@lem5064133 B) (@lem5064132 B y s)). Qed.
Lemma lem5064135 {B : Type'} (y : B) (s : B -> Prop) : (term374 B y s) = (term392 B y s).
Proof. exact (MK_COMB (@lem5064130 B y s) (@lem5064134 B y s)). Qed.
Lemma lem5064136 {B : Type'} (y : B) (s : B -> Prop) : ((term373 B y s) = (term374 B y s)) = ((term364 B y s) = (term392 B y s)).
Proof. exact (MK_COMB (@lem5064124 B y s) (@lem5064135 B y s)). Qed.
Lemma lem5064137 {B : Type'} (y : B) (s : B -> Prop) : (term364 B y s) = (term392 B y s).
Proof. exact (EQ_MP (@lem5064136 B y s) (@lem5064114 B y s)). Qed.
Lemma lem5064330 {B : Type'} (y : B) : (term365 B y) = (term393 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064137 B y s)). Qed.
Lemma lem5064331 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064332 {B : Type'} (y : B) : (term366 B y) = (term394 B y).
Proof. exact (MK_COMB (@lem5064331 B) (@lem5064330 B y)). Qed.
Lemma lem5064334 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5064335 {B : Type'} (P : type686 B) (Q : type686 B) : (term395 B P Q) = (term396 B P Q).
Proof. exact (@lem5064334 (B -> Prop) P Q). Qed.
Lemma lem5064336 {B : Type'} (y : B) : (term397 B y) = (term398 B y).
Proof. exact (@lem5064335 B (term399 B y) (term400 B y)). Qed.
Lemma lem5064337 {B : Type'} (y : B) (s : B -> Prop) : (term401 B y s) = (term386 B y s).
Proof. exact (eq_refl (term401 B y s)). Qed.
Lemma lem5064338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064339 {B : Type'} (y : B) (s : B -> Prop) : (term402 B y s) = (term388 B y s).
Proof. exact (MK_COMB (@lem5064338) (@lem5064337 B y s)). Qed.
Lemma lem5064340 {B : Type'} (y : B) (s : B -> Prop) : (term403 B y s) = (term391 B y s).
Proof. exact (eq_refl (term403 B y s)). Qed.
Lemma lem5064341 {B : Type'} (y : B) (s : B -> Prop) : (term404 B y s) = (term392 B y s).
Proof. exact (MK_COMB (@lem5064339 B y s) (@lem5064340 B y s)). Qed.
Lemma lem5064342 {B : Type'} (y : B) : (term405 B y) = (term393 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064341 B y s)). Qed.
Lemma lem5064343 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064344 {B : Type'} (y : B) : (term397 B y) = (term394 B y).
Proof. exact (MK_COMB (@lem5064343 B) (@lem5064342 B y)). Qed.
Lemma lem5064345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064346 {B : Type'} (y : B) : (term406 B y) = (term407 B y).
Proof. exact (MK_COMB (@lem5064345) (@lem5064344 B y)). Qed.
Lemma lem5064347 {B : Type'} (y : B) (s : B -> Prop) : (term401 B y s) = (term386 B y s).
Proof. exact (eq_refl (term401 B y s)). Qed.
Lemma lem5064348 {B : Type'} (y : B) : (term408 B y) = (term399 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064347 B y s)). Qed.
Lemma lem5064349 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064350 {B : Type'} (y : B) : (term409 B y) = (term410 B y).
Proof. exact (MK_COMB (@lem5064349 B) (@lem5064348 B y)). Qed.
Lemma lem5064351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064352 {B : Type'} (y : B) : (term411 B y) = (term412 B y).
Proof. exact (MK_COMB (@lem5064351) (@lem5064350 B y)). Qed.
Lemma lem5064353 {B : Type'} (y : B) (s : B -> Prop) : (term403 B y s) = (term391 B y s).
Proof. exact (eq_refl (term403 B y s)). Qed.
Lemma lem5064354 {B : Type'} (y : B) : (term413 B y) = (term400 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064353 B y s)). Qed.
Lemma lem5064355 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064356 {B : Type'} (y : B) : (term414 B y) = (term415 B y).
Proof. exact (MK_COMB (@lem5064355 B) (@lem5064354 B y)). Qed.
Lemma lem5064357 {B : Type'} (y : B) : (term398 B y) = (term416 B y).
Proof. exact (MK_COMB (@lem5064352 B y) (@lem5064356 B y)). Qed.
Lemma lem5064358 {B : Type'} (y : B) : ((term397 B y) = (term398 B y)) = ((term394 B y) = (term416 B y)).
Proof. exact (MK_COMB (@lem5064346 B y) (@lem5064357 B y)). Qed.
Lemma lem5064359 {B : Type'} (y : B) : (term394 B y) = (term416 B y).
Proof. exact (EQ_MP (@lem5064358 B y) (@lem5064336 B y)). Qed.
Lemma lem5064560 {B : Type'} (y : B) : (term366 B y) = (term416 B y).
Proof. exact (TRANS (@lem5064332 B y) (@lem5064359 B y)). Qed.
Lemma lem5064561 {B : Type'} : (term367 B) = (term417 B).
Proof. exact (fun_ext (fun y : B => @lem5064560 B y)). Qed.
Lemma lem5064562 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064563 {B : Type'} : (term368 B) = (term418 B).
Proof. exact (MK_COMB (@lem5064562 B) (@lem5064561 B)). Qed.
Lemma lem5064565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5064566 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term369 B P Q) = (term370 B P Q).
Proof. exact (@lem5064565 B P Q). Qed.
Lemma lem5064567 {B : Type'} : (term419 B) = (term420 B).
Proof. exact (@lem5064566 B (term421 B) (term422 B)). Qed.
Lemma lem5064568 {B : Type'} (y : B) : (term423 B y) = (term410 B y).
Proof. exact (eq_refl (term423 B y)). Qed.
Lemma lem5064569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064570 {B : Type'} (y : B) : (term424 B y) = (term412 B y).
Proof. exact (MK_COMB (@lem5064569) (@lem5064568 B y)). Qed.
Lemma lem5064571 {B : Type'} (y : B) : (term425 B y) = (term415 B y).
Proof. exact (eq_refl (term425 B y)). Qed.
Lemma lem5064572 {B : Type'} (y : B) : (term426 B y) = (term416 B y).
Proof. exact (MK_COMB (@lem5064570 B y) (@lem5064571 B y)). Qed.
Lemma lem5064573 {B : Type'} : (term427 B) = (term417 B).
Proof. exact (fun_ext (fun y : B => @lem5064572 B y)). Qed.
Lemma lem5064574 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064575 {B : Type'} : (term419 B) = (term418 B).
Proof. exact (MK_COMB (@lem5064574 B) (@lem5064573 B)). Qed.
Lemma lem5064576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064577 {B : Type'} : (term428 B) = (term429 B).
Proof. exact (MK_COMB (@lem5064576) (@lem5064575 B)). Qed.
Lemma lem5064578 {B : Type'} (y : B) : (term423 B y) = (term410 B y).
Proof. exact (eq_refl (term423 B y)). Qed.
Lemma lem5064579 {B : Type'} : (term430 B) = (term421 B).
Proof. exact (fun_ext (fun y : B => @lem5064578 B y)). Qed.
Lemma lem5064580 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064581 {B : Type'} : (term431 B) = (term432 B).
Proof. exact (MK_COMB (@lem5064580 B) (@lem5064579 B)). Qed.
Lemma lem5064582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064583 {B : Type'} : (term433 B) = (term434 B).
Proof. exact (MK_COMB (@lem5064582) (@lem5064581 B)). Qed.
Lemma lem5064584 {B : Type'} (y : B) : (term425 B y) = (term415 B y).
Proof. exact (eq_refl (term425 B y)). Qed.
Lemma lem5064585 {B : Type'} : (term435 B) = (term422 B).
Proof. exact (fun_ext (fun y : B => @lem5064584 B y)). Qed.
Lemma lem5064586 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064587 {B : Type'} : (term436 B) = (term437 B).
Proof. exact (MK_COMB (@lem5064586 B) (@lem5064585 B)). Qed.
Lemma lem5064588 {B : Type'} : (term420 B) = (term438 B).
Proof. exact (MK_COMB (@lem5064583 B) (@lem5064587 B)). Qed.
Lemma lem5064589 {B : Type'} : ((term419 B) = (term420 B)) = ((term418 B) = (term438 B)).
Proof. exact (MK_COMB (@lem5064577 B) (@lem5064588 B)). Qed.
Lemma lem5064590 {B : Type'} : (term418 B) = (term438 B).
Proof. exact (EQ_MP (@lem5064589 B) (@lem5064567 B)). Qed.
Lemma lem5064799 {B : Type'} : (term368 B) = (term438 B).
Proof. exact (TRANS (@lem5064563 B) (@lem5064590 B)). Qed.
Lemma lem5064801 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5064802 {B : Type'} (P : Prop) (Q : B -> Prop) : (term296 B P Q) = (term297 B P Q).
Proof. exact (@lem5064801 B P Q). Qed.
Lemma lem5064803 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term439 B y f s) = (term440 B y f s).
Proof. exact (@lem5064802 B (term441 B y f s) (term186 B y f s)). Qed.
Lemma lem5064804 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term349 B y f s x) = (term185 B y f x s).
Proof. exact (eq_refl (term349 B y f s x)). Qed.
Lemma lem5064805 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term442 B y f s) = (term186 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5064804 B y f x s)). Qed.
Lemma lem5064806 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5064807 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term443 B y f s) = (term187 B y f s).
Proof. exact (MK_COMB (@lem5064806 B) (@lem5064805 B y f s)). Qed.
Lemma lem5064808 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term354 B y f s) = (term354 B y f s).
Proof. exact (eq_refl (term354 B y f s)). Qed.
Lemma lem5064809 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term439 B y f s) = (term355 B y f s).
Proof. exact (MK_COMB (@lem5064808 B y f s) (@lem5064807 B y f s)). Qed.
Lemma lem5064810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064811 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term444 B y f s) = (term445 B y f s).
Proof. exact (MK_COMB (@lem5064810) (@lem5064809 B y f s)). Qed.
Lemma lem5064812 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term349 B y f s x) = (term185 B y f x s).
Proof. exact (eq_refl (term349 B y f s x)). Qed.
Lemma lem5064813 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term354 B y f s) = (term354 B y f s).
Proof. exact (eq_refl (term354 B y f s)). Qed.
Lemma lem5064814 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term446 B y f s x) = (term447 B y f x s).
Proof. exact (MK_COMB (@lem5064813 B y f s) (@lem5064812 B y f x s)). Qed.
Lemma lem5064815 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term448 B y f s) = (term449 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5064814 B y f x s)). Qed.
Lemma lem5064816 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5064817 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term440 B y f s) = (term450 B y f s).
Proof. exact (MK_COMB (@lem5064816 B) (@lem5064815 B y f s)). Qed.
Lemma lem5064818 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term439 B y f s) = (term440 B y f s)) = ((term355 B y f s) = (term450 B y f s)).
Proof. exact (MK_COMB (@lem5064811 B y f s) (@lem5064817 B y f s)). Qed.
Lemma lem5064819 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term355 B y f s) = (term450 B y f s).
Proof. exact (EQ_MP (@lem5064818 B y f s) (@lem5064803 B y f s)). Qed.
Lemma lem5064820 {B : Type'} (y : B) (s : B -> Prop) : (term376 B y s) = (term451 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064819 B y f s)). Qed.
Lemma lem5064821 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064822 {B : Type'} (y : B) (s : B -> Prop) : (term391 B y s) = (term452 B y s).
Proof. exact (MK_COMB (@lem5064821 B) (@lem5064820 B y s)). Qed.
Lemma lem5064824 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5064825 {B : Type'} (P : type486 B) : (term455 B P) = (term456 B P).
Proof. exact (@lem5064824 (B -> B) B P). Qed.
Lemma lem5064826 {B : Type'} (y : B) (s : B -> Prop) : (term457 B y s) = (term458 B y s).
Proof. exact (@lem5064825 B (term459 B y s)). Qed.
Lemma lem5064827 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term460 B y s f) = (term449 B y f s).
Proof. exact (eq_refl (term460 B y s f)). Qed.
Lemma lem5064828 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5064829 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) (x : B) : (term461 B y s f x) = (term462 B y f s x).
Proof. exact (MK_COMB (@lem5064827 B y f s) (@lem5064828 B x)). Qed.
Lemma lem5064830 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term462 B y f s x) = (term447 B y f x s).
Proof. exact (eq_refl (term462 B y f s x)). Qed.
Lemma lem5064831 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term461 B y s f x) = (term447 B y f x s).
Proof. exact (TRANS (@lem5064829 B y f s x) (@lem5064830 B y f x s)). Qed.
Lemma lem5064832 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term463 B y s f) = (term449 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5064831 B y f x s)). Qed.
Lemma lem5064833 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5064834 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term464 B y s f) = (term450 B y f s).
Proof. exact (MK_COMB (@lem5064833 B) (@lem5064832 B y f s)). Qed.
Lemma lem5064835 {B : Type'} (y : B) (s : B -> Prop) : (term465 B y s) = (term451 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064834 B y f s)). Qed.
Lemma lem5064836 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064837 {B : Type'} (y : B) (s : B -> Prop) : (term457 B y s) = (term452 B y s).
Proof. exact (MK_COMB (@lem5064836 B) (@lem5064835 B y s)). Qed.
Lemma lem5064838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064839 {B : Type'} (y : B) (s : B -> Prop) : (term466 B y s) = (term467 B y s).
Proof. exact (MK_COMB (@lem5064838) (@lem5064837 B y s)). Qed.
Lemma lem5064840 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term460 B y s f) = (term449 B y f s).
Proof. exact (eq_refl (term460 B y s f)). Qed.
Lemma lem5064841 {B : Type'} (x : type487 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5064842 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) (f : B -> B) : (term468 B y s x f) = (term469 B y s x f).
Proof. exact (MK_COMB (@lem5064840 B y f s) (@lem5064841 B x f)). Qed.
Lemma lem5064843 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term469 B y s x f) = (term470 B y x f s).
Proof. exact (eq_refl (term469 B y s x f)). Qed.
Lemma lem5064844 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term468 B y s x f) = (term470 B y x f s).
Proof. exact (TRANS (@lem5064842 B y s x f) (@lem5064843 B y x f s)). Qed.
Lemma lem5064845 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term471 B y s x) = (term472 B y x s).
Proof. exact (fun_ext (fun f : B -> B => @lem5064844 B y x f s)). Qed.
Lemma lem5064846 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5064847 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term473 B y s x) = (term474 B y x s).
Proof. exact (MK_COMB (@lem5064846 B) (@lem5064845 B y x s)). Qed.
Lemma lem5064848 {B : Type'} (y : B) (s : B -> Prop) : (term475 B y s) = (term476 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem5064847 B y x s)). Qed.
Lemma lem5064849 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem5064850 {B : Type'} (y : B) (s : B -> Prop) : (term458 B y s) = (term477 B y s).
Proof. exact (MK_COMB (@lem5064849 B) (@lem5064848 B y s)). Qed.
Lemma lem5064851 {B : Type'} (y : B) (s : B -> Prop) : ((term457 B y s) = (term458 B y s)) = ((term452 B y s) = (term477 B y s)).
Proof. exact (MK_COMB (@lem5064839 B y s) (@lem5064850 B y s)). Qed.
Lemma lem5064852 {B : Type'} (y : B) (s : B -> Prop) : (term452 B y s) = (term477 B y s).
Proof. exact (EQ_MP (@lem5064851 B y s) (@lem5064826 B y s)). Qed.
Lemma lem5064853 {B : Type'} (y : B) (s : B -> Prop) : (term391 B y s) = (term477 B y s).
Proof. exact (TRANS (@lem5064822 B y s) (@lem5064852 B y s)). Qed.
Lemma lem5064854 {B : Type'} (y : B) : (term400 B y) = (term478 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064853 B y s)). Qed.
Lemma lem5064855 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064856 {B : Type'} (y : B) : (term415 B y) = (term479 B y).
Proof. exact (MK_COMB (@lem5064855 B) (@lem5064854 B y)). Qed.
Lemma lem5064858 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5064859 {B : Type'} (P : type587 B) : (term480 B P) = (term481 B P).
Proof. exact (@lem5064858 (B -> Prop) (type487 B) P). Qed.
Lemma lem5064860 {B : Type'} (y : B) : (term482 B y) = (term483 B y).
Proof. exact (@lem5064859 B (term484 B y)). Qed.
Lemma lem5064861 {B : Type'} (y : B) (s : B -> Prop) : (term485 B y s) = (term476 B y s).
Proof. exact (eq_refl (term485 B y s)). Qed.
Lemma lem5064862 {B : Type'} (x : type487 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5064863 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) : (term486 B y s x) = (term487 B y s x).
Proof. exact (MK_COMB (@lem5064861 B y s) (@lem5064862 B x)). Qed.
Lemma lem5064864 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term487 B y s x) = (term474 B y x s).
Proof. exact (eq_refl (term487 B y s x)). Qed.
Lemma lem5064865 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term486 B y s x) = (term474 B y x s).
Proof. exact (TRANS (@lem5064863 B y s x) (@lem5064864 B y x s)). Qed.
Lemma lem5064866 {B : Type'} (y : B) (s : B -> Prop) : (term488 B y s) = (term476 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem5064865 B y x s)). Qed.
Lemma lem5064867 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem5064868 {B : Type'} (y : B) (s : B -> Prop) : (term489 B y s) = (term477 B y s).
Proof. exact (MK_COMB (@lem5064867 B) (@lem5064866 B y s)). Qed.
Lemma lem5064869 {B : Type'} (y : B) : (term490 B y) = (term478 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064868 B y s)). Qed.
Lemma lem5064870 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064871 {B : Type'} (y : B) : (term482 B y) = (term479 B y).
Proof. exact (MK_COMB (@lem5064870 B) (@lem5064869 B y)). Qed.
Lemma lem5064872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064873 {B : Type'} (y : B) : (term491 B y) = (term492 B y).
Proof. exact (MK_COMB (@lem5064872) (@lem5064871 B y)). Qed.
Lemma lem5064874 {B : Type'} (y : B) (s : B -> Prop) : (term485 B y s) = (term476 B y s).
Proof. exact (eq_refl (term485 B y s)). Qed.
Lemma lem5064875 {B : Type'} (x : type623 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5064876 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term493 B y x s) = (term494 B y x s).
Proof. exact (MK_COMB (@lem5064874 B y s) (@lem5064875 B x s)). Qed.
Lemma lem5064877 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term494 B y x s) = (term495 B y x s).
Proof. exact (eq_refl (term494 B y x s)). Qed.
Lemma lem5064878 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term493 B y x s) = (term495 B y x s).
Proof. exact (TRANS (@lem5064876 B y x s) (@lem5064877 B y x s)). Qed.
Lemma lem5064879 {B : Type'} (y : B) (x : type623 B) : (term496 B y x) = (term497 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5064878 B y x s)). Qed.
Lemma lem5064880 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5064881 {B : Type'} (y : B) (x : type623 B) : (term498 B y x) = (term499 B y x).
Proof. exact (MK_COMB (@lem5064880 B) (@lem5064879 B y x)). Qed.
Lemma lem5064882 {B : Type'} (y : B) : (term500 B y) = (term501 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem5064881 B y x)). Qed.
Lemma lem5064883 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5064884 {B : Type'} (y : B) : (term483 B y) = (term502 B y).
Proof. exact (MK_COMB (@lem5064883 B) (@lem5064882 B y)). Qed.
Lemma lem5064885 {B : Type'} (y : B) : ((term482 B y) = (term483 B y)) = ((term479 B y) = (term502 B y)).
Proof. exact (MK_COMB (@lem5064873 B y) (@lem5064884 B y)). Qed.
Lemma lem5064886 {B : Type'} (y : B) : (term479 B y) = (term502 B y).
Proof. exact (EQ_MP (@lem5064885 B y) (@lem5064860 B y)). Qed.
Lemma lem5064887 {B : Type'} (y : B) : (term415 B y) = (term502 B y).
Proof. exact (TRANS (@lem5064856 B y) (@lem5064886 B y)). Qed.
Lemma lem5064888 {B : Type'} : (term422 B) = (term503 B).
Proof. exact (fun_ext (fun y : B => @lem5064887 B y)). Qed.
Lemma lem5064889 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064890 {B : Type'} : (term437 B) = (term504 B).
Proof. exact (MK_COMB (@lem5064889 B) (@lem5064888 B)). Qed.
Lemma lem5064892 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5064893 {B : Type'} (P : type1356 B) : (term505 B P) = (term506 B P).
Proof. exact (@lem5064892 B (type623 B) P). Qed.
Lemma lem5064894 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (@lem5064893 B (term509 B)). Qed.
Lemma lem5064895 {B : Type'} (y : B) : (term510 B y) = (term501 B y).
Proof. exact (eq_refl (term510 B y)). Qed.
Lemma lem5064896 {B : Type'} (x : type623 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5064897 {B : Type'} (y : B) (x : type623 B) : (term511 B y x) = (term512 B y x).
Proof. exact (MK_COMB (@lem5064895 B y) (@lem5064896 B x)). Qed.
Lemma lem5064898 {B : Type'} (y : B) (x : type623 B) : (term512 B y x) = (term499 B y x).
Proof. exact (eq_refl (term512 B y x)). Qed.
Lemma lem5064899 {B : Type'} (y : B) (x : type623 B) : (term511 B y x) = (term499 B y x).
Proof. exact (TRANS (@lem5064897 B y x) (@lem5064898 B y x)). Qed.
Lemma lem5064900 {B : Type'} (y : B) : (term513 B y) = (term501 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem5064899 B y x)). Qed.
Lemma lem5064901 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5064902 {B : Type'} (y : B) : (term514 B y) = (term502 B y).
Proof. exact (MK_COMB (@lem5064901 B) (@lem5064900 B y)). Qed.
Lemma lem5064903 {B : Type'} : (term515 B) = (term503 B).
Proof. exact (fun_ext (fun y : B => @lem5064902 B y)). Qed.
Lemma lem5064904 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064905 {B : Type'} : (term507 B) = (term504 B).
Proof. exact (MK_COMB (@lem5064904 B) (@lem5064903 B)). Qed.
Lemma lem5064906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064907 {B : Type'} : (term516 B) = (term517 B).
Proof. exact (MK_COMB (@lem5064906) (@lem5064905 B)). Qed.
Lemma lem5064908 {B : Type'} (y : B) : (term510 B y) = (term501 B y).
Proof. exact (eq_refl (term510 B y)). Qed.
Lemma lem5064909 {B : Type'} (x : type1361 B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5064910 {B : Type'} (x : type1361 B) (y : B) : (term518 B x y) = (term519 B x y).
Proof. exact (MK_COMB (@lem5064908 B y) (@lem5064909 B x y)). Qed.
Lemma lem5064911 {B : Type'} (x : type1361 B) (y : B) : (term519 B x y) = (term520 B x y).
Proof. exact (eq_refl (term519 B x y)). Qed.
Lemma lem5064912 {B : Type'} (x : type1361 B) (y : B) : (term518 B x y) = (term520 B x y).
Proof. exact (TRANS (@lem5064910 B x y) (@lem5064911 B x y)). Qed.
Lemma lem5064913 {B : Type'} (x : type1361 B) : (term521 B x) = (term522 B x).
Proof. exact (fun_ext (fun y : B => @lem5064912 B x y)). Qed.
Lemma lem5064914 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5064915 {B : Type'} (x : type1361 B) : (term523 B x) = (term524 B x).
Proof. exact (MK_COMB (@lem5064914 B) (@lem5064913 B x)). Qed.
Lemma lem5064916 {B : Type'} : (term525 B) = (term526 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5064915 B x)). Qed.
Lemma lem5064917 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5064918 {B : Type'} : (term508 B) = (term527 B).
Proof. exact (MK_COMB (@lem5064917 B) (@lem5064916 B)). Qed.
Lemma lem5064919 {B : Type'} : ((term507 B) = (term508 B)) = ((term504 B) = (term527 B)).
Proof. exact (MK_COMB (@lem5064907 B) (@lem5064918 B)). Qed.
Lemma lem5064920 {B : Type'} : (term504 B) = (term527 B).
Proof. exact (EQ_MP (@lem5064919 B) (@lem5064894 B)). Qed.
Lemma lem5064921 {B : Type'} : (term437 B) = (term527 B).
Proof. exact (TRANS (@lem5064890 B) (@lem5064920 B)). Qed.
Lemma lem5064922 {B : Type'} : (term434 B) = (term434 B).
Proof. exact (eq_refl (term434 B)). Qed.
Lemma lem5064923 {B : Type'} : (term438 B) = (term528 B).
Proof. exact (MK_COMB (@lem5064922 B) (@lem5064921 B)). Qed.
Lemma lem5064925 {A : Type'} (P : Prop) (Q : A -> Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5064926 {B : Type'} (P : Prop) (Q : type391 B) : (term529 B P Q) = (term530 B P Q).
Proof. exact (@lem5064925 (type1361 B) P Q). Qed.
Lemma lem5064927 {B : Type'} : (term531 B) = (term532 B).
Proof. exact (@lem5064926 B (term432 B) (term526 B)). Qed.
Lemma lem5064928 {B : Type'} (x : type1361 B) : (term533 B x) = (term524 B x).
Proof. exact (eq_refl (term533 B x)). Qed.
Lemma lem5064929 {B : Type'} : (term534 B) = (term526 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5064928 B x)). Qed.
Lemma lem5064930 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5064931 {B : Type'} : (term535 B) = (term527 B).
Proof. exact (MK_COMB (@lem5064930 B) (@lem5064929 B)). Qed.
Lemma lem5064932 {B : Type'} : (term434 B) = (term434 B).
Proof. exact (eq_refl (term434 B)). Qed.
Lemma lem5064933 {B : Type'} : (term531 B) = (term528 B).
Proof. exact (MK_COMB (@lem5064932 B) (@lem5064931 B)). Qed.
Lemma lem5064934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5064935 {B : Type'} : (term536 B) = (term537 B).
Proof. exact (MK_COMB (@lem5064934) (@lem5064933 B)). Qed.
Lemma lem5064936 {B : Type'} (x : type1361 B) : (term533 B x) = (term524 B x).
Proof. exact (eq_refl (term533 B x)). Qed.
Lemma lem5064937 {B : Type'} : (term434 B) = (term434 B).
Proof. exact (eq_refl (term434 B)). Qed.
Lemma lem5064938 {B : Type'} (x : type1361 B) : (term538 B x) = (term539 B x).
Proof. exact (MK_COMB (@lem5064937 B) (@lem5064936 B x)). Qed.
Lemma lem5064939 {B : Type'} : (term540 B) = (term541 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5064938 B x)). Qed.
Lemma lem5064940 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5064941 {B : Type'} : (term532 B) = (term542 B).
Proof. exact (MK_COMB (@lem5064940 B) (@lem5064939 B)). Qed.
Lemma lem5064942 {B : Type'} : ((term531 B) = (term532 B)) = ((term528 B) = (term542 B)).
Proof. exact (MK_COMB (@lem5064935 B) (@lem5064941 B)). Qed.
Lemma lem5064943 {B : Type'} : (term528 B) = (term542 B).
Proof. exact (EQ_MP (@lem5064942 B) (@lem5064927 B)). Qed.
Lemma lem5064944 {B : Type'} : (term438 B) = (term542 B).
Proof. exact (TRANS (@lem5064923 B) (@lem5064943 B)). Qed.
Lemma lem5064945 {B : Type'} : (term368 B) = (term542 B).
Proof. exact (TRANS (@lem5064799 B) (@lem5064944 B)). Qed.
Lemma lem5064946 {B : Type'} : (term149 B) = (term542 B).
Proof. exact (TRANS (@lem5064102 B) (@lem5064945 B)). Qed.
Lemma lem5064947 {B : Type'} (h1 : term149 B) : term542 B.
Proof. exact (EQ_MP (@lem5064946 B) (@lem5061863 B h1)). Qed.
Lemma lem5064958 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term735 A s x t) = (term736 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5064963 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term178 A s x t) = (term737 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5064964 {A : Type'} (P : A -> Prop) : (term233 A P) = (term234 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5064965 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term738 A s t) = (term739 A s t).
Proof. exact (@lem5064964 A (term179 A s t)). Qed.
Lemma lem5064966 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term740 A s t x) = (term178 A s x t).
Proof. exact (eq_refl (term740 A s t x)). Qed.
Lemma lem5064967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5064968 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term741 A s t x) = (term735 A s x t).
Proof. exact (MK_COMB (@lem5064967) (@lem5064966 A s x t)). Qed.
Lemma lem5064969 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term741 A s t x) = (term736 A s x t).
Proof. exact (TRANS (@lem5064968 A s x t) (@lem5064958 A s x t)). Qed.
Lemma lem5064970 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term742 A s t) = (term743 A s t).
Proof. exact (fun_ext (fun x : A => @lem5064969 A s x t)). Qed.
Lemma lem5064971 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5064972 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term739 A s t) = (term744 A s t).
Proof. exact (MK_COMB (@lem5064971 A) (@lem5064970 A s t)). Qed.
Lemma lem5064973 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term738 A s t) = (term744 A s t).
Proof. exact (TRANS (@lem5064965 A s t) (@lem5064972 A s t)). Qed.
Lemma lem5064974 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term179 A s t) = (term745 A s t).
Proof. exact (fun_ext (fun x : A => @lem5064963 A s x t)). Qed.
Lemma lem5064975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5064976 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term180 A s t) = (term746 A s t).
Proof. exact (MK_COMB (@lem5064975 A) (@lem5064974 A s t)). Qed.
Lemma lem5064978 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term747 A s t) = (term747 A s t).
Proof. exact (eq_refl (term747 A s t)). Qed.
Lemma lem5064979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term748 A s t) = (term749 A s t).
Proof. exact (MK_COMB (@lem5064978 A s t) (@lem5064976 A s t)). Qed.
Lemma lem5064981 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term750 A s t) = (term750 A s t).
Proof. exact (eq_refl (term750 A s t)). Qed.
Lemma lem5064982 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term751 A s t) = (term752 A s t).
Proof. exact (MK_COMB (@lem5064981 A s t) (@lem5064973 A s t)). Qed.
Lemma lem5064983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5064984 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term753 A s t) = (term754 A s t).
Proof. exact (MK_COMB (@lem5064983) (@lem5064982 A s t)). Qed.
Lemma lem5064985 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term755 A s t) = (term756 A s t).
Proof. exact (MK_COMB (@lem5064984 A s t) (@lem5064979 A s t)). Qed.
Lemma lem5064986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term180 A s t)) = (term755 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term180 A s t)). Qed.
Lemma lem5064987 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term180 A s t)) = (term756 A s t).
Proof. exact (TRANS (@lem5064986 A s t) (@lem5064985 A s t)). Qed.
Lemma lem5064988 {A : Type'} (s : A -> Prop) : (term182 A s) = (term757 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5064987 A s t)). Qed.
Lemma lem5064989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5064990 {A : Type'} (s : A -> Prop) : (term183 A s) = (term758 A s).
Proof. exact (MK_COMB (@lem5064989 A) (@lem5064988 A s)). Qed.
Lemma lem5064991 {A : Type'} : (term184 A) = (term759 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5064990 A s)). Qed.
Lemma lem5064992 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5064993 {A : Type'} : (term148 A) = (term760 A).
Proof. exact (MK_COMB (@lem5064992 A) (@lem5064991 A)). Qed.
Lemma lem5064999 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5065000 {A : Type'} (P : type686 A) (Q : type686 A) : (term395 A P Q) = (term396 A P Q).
Proof. exact (@lem5064999 (A -> Prop) P Q). Qed.
Lemma lem5065001 {A : Type'} (s : A -> Prop) : (term761 A s) = (term762 A s).
Proof. exact (@lem5065000 A (term763 A s) (term764 A s)). Qed.
Lemma lem5065002 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term765 A s t) = (term752 A s t).
Proof. exact (eq_refl (term765 A s t)). Qed.
Lemma lem5065003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term766 A s t) = (term754 A s t).
Proof. exact (MK_COMB (@lem5065003) (@lem5065002 A s t)). Qed.
Lemma lem5065005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term767 A s t) = (term749 A s t).
Proof. exact (eq_refl (term767 A s t)). Qed.
Lemma lem5065006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term768 A s t) = (term756 A s t).
Proof. exact (MK_COMB (@lem5065004 A s t) (@lem5065005 A s t)). Qed.
Lemma lem5065007 {A : Type'} (s : A -> Prop) : (term769 A s) = (term757 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065006 A s t)). Qed.
Lemma lem5065008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065009 {A : Type'} (s : A -> Prop) : (term761 A s) = (term758 A s).
Proof. exact (MK_COMB (@lem5065008 A) (@lem5065007 A s)). Qed.
Lemma lem5065010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065011 {A : Type'} (s : A -> Prop) : (term770 A s) = (term771 A s).
Proof. exact (MK_COMB (@lem5065010) (@lem5065009 A s)). Qed.
Lemma lem5065012 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term765 A s t) = (term752 A s t).
Proof. exact (eq_refl (term765 A s t)). Qed.
Lemma lem5065013 {A : Type'} (s : A -> Prop) : (term772 A s) = (term763 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065012 A s t)). Qed.
Lemma lem5065014 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065015 {A : Type'} (s : A -> Prop) : (term773 A s) = (term774 A s).
Proof. exact (MK_COMB (@lem5065014 A) (@lem5065013 A s)). Qed.
Lemma lem5065016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065017 {A : Type'} (s : A -> Prop) : (term775 A s) = (term776 A s).
Proof. exact (MK_COMB (@lem5065016) (@lem5065015 A s)). Qed.
Lemma lem5065018 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term767 A s t) = (term749 A s t).
Proof. exact (eq_refl (term767 A s t)). Qed.
Lemma lem5065019 {A : Type'} (s : A -> Prop) : (term777 A s) = (term764 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065018 A s t)). Qed.
Lemma lem5065020 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065021 {A : Type'} (s : A -> Prop) : (term778 A s) = (term779 A s).
Proof. exact (MK_COMB (@lem5065020 A) (@lem5065019 A s)). Qed.
Lemma lem5065022 {A : Type'} (s : A -> Prop) : (term762 A s) = (term780 A s).
Proof. exact (MK_COMB (@lem5065017 A s) (@lem5065021 A s)). Qed.
Lemma lem5065023 {A : Type'} (s : A -> Prop) : ((term761 A s) = (term762 A s)) = ((term758 A s) = (term780 A s)).
Proof. exact (MK_COMB (@lem5065011 A s) (@lem5065022 A s)). Qed.
Lemma lem5065024 {A : Type'} (s : A -> Prop) : (term758 A s) = (term780 A s).
Proof. exact (EQ_MP (@lem5065023 A s) (@lem5065001 A s)). Qed.
Lemma lem5065217 {A : Type'} : (term759 A) = (term781 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065024 A s)). Qed.
Lemma lem5065218 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065219 {A : Type'} : (term760 A) = (term782 A).
Proof. exact (MK_COMB (@lem5065218 A) (@lem5065217 A)). Qed.
Lemma lem5065221 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5065222 {A : Type'} (P : type686 A) (Q : type686 A) : (term395 A P Q) = (term396 A P Q).
Proof. exact (@lem5065221 (A -> Prop) P Q). Qed.
Lemma lem5065223 {A : Type'} : (term783 A) = (term784 A).
Proof. exact (@lem5065222 A (term785 A) (term786 A)). Qed.
Lemma lem5065224 {A : Type'} (s : A -> Prop) : (term787 A s) = (term774 A s).
Proof. exact (eq_refl (term787 A s)). Qed.
Lemma lem5065225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065226 {A : Type'} (s : A -> Prop) : (term788 A s) = (term776 A s).
Proof. exact (MK_COMB (@lem5065225) (@lem5065224 A s)). Qed.
Lemma lem5065227 {A : Type'} (s : A -> Prop) : (term789 A s) = (term779 A s).
Proof. exact (eq_refl (term789 A s)). Qed.
Lemma lem5065228 {A : Type'} (s : A -> Prop) : (term790 A s) = (term780 A s).
Proof. exact (MK_COMB (@lem5065226 A s) (@lem5065227 A s)). Qed.
Lemma lem5065229 {A : Type'} : (term791 A) = (term781 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065228 A s)). Qed.
Lemma lem5065230 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065231 {A : Type'} : (term783 A) = (term782 A).
Proof. exact (MK_COMB (@lem5065230 A) (@lem5065229 A)). Qed.
Lemma lem5065232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065233 {A : Type'} : (term792 A) = (term793 A).
Proof. exact (MK_COMB (@lem5065232) (@lem5065231 A)). Qed.
Lemma lem5065234 {A : Type'} (s : A -> Prop) : (term787 A s) = (term774 A s).
Proof. exact (eq_refl (term787 A s)). Qed.
Lemma lem5065235 {A : Type'} : (term794 A) = (term785 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065234 A s)). Qed.
Lemma lem5065236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065237 {A : Type'} : (term795 A) = (term796 A).
Proof. exact (MK_COMB (@lem5065236 A) (@lem5065235 A)). Qed.
Lemma lem5065238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065239 {A : Type'} : (term797 A) = (term798 A).
Proof. exact (MK_COMB (@lem5065238) (@lem5065237 A)). Qed.
Lemma lem5065240 {A : Type'} (s : A -> Prop) : (term789 A s) = (term779 A s).
Proof. exact (eq_refl (term789 A s)). Qed.
Lemma lem5065241 {A : Type'} : (term799 A) = (term786 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065240 A s)). Qed.
Lemma lem5065242 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065243 {A : Type'} : (term800 A) = (term801 A).
Proof. exact (MK_COMB (@lem5065242 A) (@lem5065241 A)). Qed.
Lemma lem5065244 {A : Type'} : (term784 A) = (term802 A).
Proof. exact (MK_COMB (@lem5065239 A) (@lem5065243 A)). Qed.
Lemma lem5065245 {A : Type'} : ((term783 A) = (term784 A)) = ((term782 A) = (term802 A)).
Proof. exact (MK_COMB (@lem5065233 A) (@lem5065244 A)). Qed.
Lemma lem5065246 {A : Type'} : (term782 A) = (term802 A).
Proof. exact (EQ_MP (@lem5065245 A) (@lem5065223 A)). Qed.
Lemma lem5065447 {A : Type'} : (term760 A) = (term802 A).
Proof. exact (TRANS (@lem5065219 A) (@lem5065246 A)). Qed.
Lemma lem5065449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5065450 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem5065449 A P Q). Qed.
Lemma lem5065451 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term803 A s t) = (term804 A s t).
Proof. exact (@lem5065450 A (@SUBSET A s t) (term743 A s t)). Qed.
Lemma lem5065452 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term805 A s t x) = (term736 A s x t).
Proof. exact (eq_refl (term805 A s t x)). Qed.
Lemma lem5065453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term806 A s t) = (term743 A s t).
Proof. exact (fun_ext (fun x : A => @lem5065452 A s x t)). Qed.
Lemma lem5065454 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5065455 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term807 A s t) = (term744 A s t).
Proof. exact (MK_COMB (@lem5065454 A) (@lem5065453 A s t)). Qed.
Lemma lem5065456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term750 A s t) = (term750 A s t).
Proof. exact (eq_refl (term750 A s t)). Qed.
Lemma lem5065457 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term803 A s t) = (term752 A s t).
Proof. exact (MK_COMB (@lem5065456 A s t) (@lem5065455 A s t)). Qed.
Lemma lem5065458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065459 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term808 A s t) = (term809 A s t).
Proof. exact (MK_COMB (@lem5065458) (@lem5065457 A s t)). Qed.
Lemma lem5065460 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term805 A s t x) = (term736 A s x t).
Proof. exact (eq_refl (term805 A s t x)). Qed.
Lemma lem5065461 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term750 A s t) = (term750 A s t).
Proof. exact (eq_refl (term750 A s t)). Qed.
Lemma lem5065462 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term810 A s t x) = (term811 A s x t).
Proof. exact (MK_COMB (@lem5065461 A s t) (@lem5065460 A s x t)). Qed.
Lemma lem5065463 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term812 A s t) = (term813 A s t).
Proof. exact (fun_ext (fun x : A => @lem5065462 A s x t)). Qed.
Lemma lem5065464 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5065465 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term804 A s t) = (term814 A s t).
Proof. exact (MK_COMB (@lem5065464 A) (@lem5065463 A s t)). Qed.
Lemma lem5065466 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term803 A s t) = (term804 A s t)) = ((term752 A s t) = (term814 A s t)).
Proof. exact (MK_COMB (@lem5065459 A s t) (@lem5065465 A s t)). Qed.
Lemma lem5065467 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term752 A s t) = (term814 A s t).
Proof. exact (EQ_MP (@lem5065466 A s t) (@lem5065451 A s t)). Qed.
Lemma lem5065468 {A : Type'} (s : A -> Prop) : (term763 A s) = (term815 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065467 A s t)). Qed.
Lemma lem5065469 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065470 {A : Type'} (s : A -> Prop) : (term774 A s) = (term816 A s).
Proof. exact (MK_COMB (@lem5065469 A) (@lem5065468 A s)). Qed.
Lemma lem5065472 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5065473 {A : Type'} (P : type672 A) : (term817 A P) = (term818 A P).
Proof. exact (@lem5065472 (A -> Prop) A P). Qed.
Lemma lem5065474 {A : Type'} (s : A -> Prop) : (term819 A s) = (term820 A s).
Proof. exact (@lem5065473 A (term821 A s)). Qed.
Lemma lem5065475 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term822 A s t) = (term813 A s t).
Proof. exact (eq_refl (term822 A s t)). Qed.
Lemma lem5065476 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5065477 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term823 A s t x) = (term824 A s t x).
Proof. exact (MK_COMB (@lem5065475 A s t) (@lem5065476 A x)). Qed.
Lemma lem5065478 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term824 A s t x) = (term811 A s x t).
Proof. exact (eq_refl (term824 A s t x)). Qed.
Lemma lem5065479 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term823 A s t x) = (term811 A s x t).
Proof. exact (TRANS (@lem5065477 A s t x) (@lem5065478 A s x t)). Qed.
Lemma lem5065480 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term825 A s t) = (term813 A s t).
Proof. exact (fun_ext (fun x : A => @lem5065479 A s x t)). Qed.
Lemma lem5065481 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5065482 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term826 A s t) = (term814 A s t).
Proof. exact (MK_COMB (@lem5065481 A) (@lem5065480 A s t)). Qed.
Lemma lem5065483 {A : Type'} (s : A -> Prop) : (term827 A s) = (term815 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065482 A s t)). Qed.
Lemma lem5065484 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065485 {A : Type'} (s : A -> Prop) : (term819 A s) = (term816 A s).
Proof. exact (MK_COMB (@lem5065484 A) (@lem5065483 A s)). Qed.
Lemma lem5065486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065487 {A : Type'} (s : A -> Prop) : (term828 A s) = (term829 A s).
Proof. exact (MK_COMB (@lem5065486) (@lem5065485 A s)). Qed.
Lemma lem5065488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term822 A s t) = (term813 A s t).
Proof. exact (eq_refl (term822 A s t)). Qed.
Lemma lem5065489 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem5065490 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term830 A s x t) = (term831 A s x t).
Proof. exact (MK_COMB (@lem5065488 A s t) (@lem5065489 A x t)). Qed.
Lemma lem5065491 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term831 A s x t) = (term832 A s x t).
Proof. exact (eq_refl (term831 A s x t)). Qed.
Lemma lem5065492 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term830 A s x t) = (term832 A s x t).
Proof. exact (TRANS (@lem5065490 A s x t) (@lem5065491 A s x t)). Qed.
Lemma lem5065493 {A : Type'} (s : A -> Prop) (x : type684 A) : (term833 A s x) = (term834 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5065492 A s x t)). Qed.
Lemma lem5065494 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065495 {A : Type'} (s : A -> Prop) (x : type684 A) : (term835 A s x) = (term836 A s x).
Proof. exact (MK_COMB (@lem5065494 A) (@lem5065493 A s x)). Qed.
Lemma lem5065496 {A : Type'} (s : A -> Prop) : (term837 A s) = (term838 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5065495 A s x)). Qed.
Lemma lem5065497 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5065498 {A : Type'} (s : A -> Prop) : (term820 A s) = (term839 A s).
Proof. exact (MK_COMB (@lem5065497 A) (@lem5065496 A s)). Qed.
Lemma lem5065499 {A : Type'} (s : A -> Prop) : ((term819 A s) = (term820 A s)) = ((term816 A s) = (term839 A s)).
Proof. exact (MK_COMB (@lem5065487 A s) (@lem5065498 A s)). Qed.
Lemma lem5065500 {A : Type'} (s : A -> Prop) : (term816 A s) = (term839 A s).
Proof. exact (EQ_MP (@lem5065499 A s) (@lem5065474 A s)). Qed.
Lemma lem5065501 {A : Type'} (s : A -> Prop) : (term774 A s) = (term839 A s).
Proof. exact (TRANS (@lem5065470 A s) (@lem5065500 A s)). Qed.
Lemma lem5065502 {A : Type'} : (term785 A) = (term840 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065501 A s)). Qed.
Lemma lem5065503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065504 {A : Type'} : (term796 A) = (term841 A).
Proof. exact (MK_COMB (@lem5065503 A) (@lem5065502 A)). Qed.
Lemma lem5065506 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5065507 {A : Type'} (P : type597 A) : (term842 A P) = (term843 A P).
Proof. exact (@lem5065506 (A -> Prop) (type684 A) P). Qed.
Lemma lem5065508 {A : Type'} : (term844 A) = (term845 A).
Proof. exact (@lem5065507 A (term846 A)). Qed.
Lemma lem5065509 {A : Type'} (s : A -> Prop) : (term847 A s) = (term838 A s).
Proof. exact (eq_refl (term847 A s)). Qed.
Lemma lem5065510 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5065511 {A : Type'} (s : A -> Prop) (x : type684 A) : (term848 A s x) = (term849 A s x).
Proof. exact (MK_COMB (@lem5065509 A s) (@lem5065510 A x)). Qed.
Lemma lem5065512 {A : Type'} (s : A -> Prop) (x : type684 A) : (term849 A s x) = (term836 A s x).
Proof. exact (eq_refl (term849 A s x)). Qed.
Lemma lem5065513 {A : Type'} (s : A -> Prop) (x : type684 A) : (term848 A s x) = (term836 A s x).
Proof. exact (TRANS (@lem5065511 A s x) (@lem5065512 A s x)). Qed.
Lemma lem5065514 {A : Type'} (s : A -> Prop) : (term850 A s) = (term838 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5065513 A s x)). Qed.
Lemma lem5065515 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5065516 {A : Type'} (s : A -> Prop) : (term851 A s) = (term839 A s).
Proof. exact (MK_COMB (@lem5065515 A) (@lem5065514 A s)). Qed.
Lemma lem5065517 {A : Type'} : (term852 A) = (term840 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065516 A s)). Qed.
Lemma lem5065518 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065519 {A : Type'} : (term844 A) = (term841 A).
Proof. exact (MK_COMB (@lem5065518 A) (@lem5065517 A)). Qed.
Lemma lem5065520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065521 {A : Type'} : (term853 A) = (term854 A).
Proof. exact (MK_COMB (@lem5065520) (@lem5065519 A)). Qed.
Lemma lem5065522 {A : Type'} (s : A -> Prop) : (term847 A s) = (term838 A s).
Proof. exact (eq_refl (term847 A s)). Qed.
Lemma lem5065523 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5065524 {A : Type'} (x : type638 A) (s : A -> Prop) : (term855 A x s) = (term856 A x s).
Proof. exact (MK_COMB (@lem5065522 A s) (@lem5065523 A x s)). Qed.
Lemma lem5065525 {A : Type'} (x : type638 A) (s : A -> Prop) : (term856 A x s) = (term857 A x s).
Proof. exact (eq_refl (term856 A x s)). Qed.
Lemma lem5065526 {A : Type'} (x : type638 A) (s : A -> Prop) : (term855 A x s) = (term857 A x s).
Proof. exact (TRANS (@lem5065524 A x s) (@lem5065525 A x s)). Qed.
Lemma lem5065527 {A : Type'} (x : type638 A) : (term858 A x) = (term859 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5065526 A x s)). Qed.
Lemma lem5065528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5065529 {A : Type'} (x : type638 A) : (term860 A x) = (term861 A x).
Proof. exact (MK_COMB (@lem5065528 A) (@lem5065527 A x)). Qed.
Lemma lem5065530 {A : Type'} : (term862 A) = (term863 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5065529 A x)). Qed.
Lemma lem5065531 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5065532 {A : Type'} : (term845 A) = (term864 A).
Proof. exact (MK_COMB (@lem5065531 A) (@lem5065530 A)). Qed.
Lemma lem5065533 {A : Type'} : ((term844 A) = (term845 A)) = ((term841 A) = (term864 A)).
Proof. exact (MK_COMB (@lem5065521 A) (@lem5065532 A)). Qed.
Lemma lem5065534 {A : Type'} : (term841 A) = (term864 A).
Proof. exact (EQ_MP (@lem5065533 A) (@lem5065508 A)). Qed.
Lemma lem5065535 {A : Type'} : (term796 A) = (term864 A).
Proof. exact (TRANS (@lem5065504 A) (@lem5065534 A)). Qed.
Lemma lem5065536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065537 {A : Type'} : (term798 A) = (term865 A).
Proof. exact (MK_COMB (@lem5065536) (@lem5065535 A)). Qed.
Lemma lem5065538 {A : Type'} : (term801 A) = (term801 A).
Proof. exact (eq_refl (term801 A)). Qed.
Lemma lem5065539 {A : Type'} : (term802 A) = (term866 A).
Proof. exact (MK_COMB (@lem5065537 A) (@lem5065538 A)). Qed.
Lemma lem5065541 {A : Type'} (P : A -> Prop) (Q : Prop) : (term867 A P Q) = (term868 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5065542 {A : Type'} (P : type139 A) (Q : Prop) : (term869 A P Q) = (term870 A P Q).
Proof. exact (@lem5065541 (type638 A) P Q). Qed.
Lemma lem5065543 {A : Type'} : (term871 A) = (term872 A).
Proof. exact (@lem5065542 A (term863 A) (term801 A)). Qed.
Lemma lem5065544 {A : Type'} (x : type638 A) : (term873 A x) = (term861 A x).
Proof. exact (eq_refl (term873 A x)). Qed.
Lemma lem5065545 {A : Type'} : (term874 A) = (term863 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5065544 A x)). Qed.
Lemma lem5065546 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5065547 {A : Type'} : (term875 A) = (term864 A).
Proof. exact (MK_COMB (@lem5065546 A) (@lem5065545 A)). Qed.
Lemma lem5065548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065549 {A : Type'} : (term876 A) = (term865 A).
Proof. exact (MK_COMB (@lem5065548) (@lem5065547 A)). Qed.
Lemma lem5065550 {A : Type'} : (term801 A) = (term801 A).
Proof. exact (eq_refl (term801 A)). Qed.
Lemma lem5065551 {A : Type'} : (term871 A) = (term866 A).
Proof. exact (MK_COMB (@lem5065549 A) (@lem5065550 A)). Qed.
Lemma lem5065552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065553 {A : Type'} : (term877 A) = (term878 A).
Proof. exact (MK_COMB (@lem5065552) (@lem5065551 A)). Qed.
Lemma lem5065554 {A : Type'} (x : type638 A) : (term873 A x) = (term861 A x).
Proof. exact (eq_refl (term873 A x)). Qed.
Lemma lem5065555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065556 {A : Type'} (x : type638 A) : (term879 A x) = (term880 A x).
Proof. exact (MK_COMB (@lem5065555) (@lem5065554 A x)). Qed.
Lemma lem5065557 {A : Type'} : (term801 A) = (term801 A).
Proof. exact (eq_refl (term801 A)). Qed.
Lemma lem5065558 {A : Type'} (x : type638 A) : (term881 A x) = (term882 A x).
Proof. exact (MK_COMB (@lem5065556 A x) (@lem5065557 A)). Qed.
Lemma lem5065559 {A : Type'} : (term883 A) = (term884 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5065558 A x)). Qed.
Lemma lem5065560 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5065561 {A : Type'} : (term872 A) = (term885 A).
Proof. exact (MK_COMB (@lem5065560 A) (@lem5065559 A)). Qed.
Lemma lem5065562 {A : Type'} : ((term871 A) = (term872 A)) = ((term866 A) = (term885 A)).
Proof. exact (MK_COMB (@lem5065553 A) (@lem5065561 A)). Qed.
Lemma lem5065563 {A : Type'} : (term866 A) = (term885 A).
Proof. exact (EQ_MP (@lem5065562 A) (@lem5065543 A)). Qed.
Lemma lem5065564 {A : Type'} : (term802 A) = (term885 A).
Proof. exact (TRANS (@lem5065539 A) (@lem5065563 A)). Qed.
Lemma lem5065565 {A : Type'} : (term760 A) = (term885 A).
Proof. exact (TRANS (@lem5065447 A) (@lem5065564 A)). Qed.
Lemma lem5065566 {A : Type'} : (term148 A) = (term885 A).
Proof. exact (TRANS (@lem5064993 A) (@lem5065565 A)). Qed.
Lemma lem5065567 {A : Type'} (h1 : term148 A) : term885 A.
Proof. exact (EQ_MP (@lem5065566 A) (@lem5061864 A h1)). Qed.
Lemma lem5065578 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term735 B s x t) = (term736 B s x t).
Proof. exact (@lem17362 (@IN B x s) (@IN B x t)). Qed.
Lemma lem5065583 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term178 B s x t) = (term737 B s x t).
Proof. exact (@lem17265 (@IN B x s) (@IN B x t)). Qed.
Lemma lem5065584 {B : Type'} (P : B -> Prop) : (term233 B P) = (term234 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5065585 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term738 B s t) = (term739 B s t).
Proof. exact (@lem5065584 B (term179 B s t)). Qed.
Lemma lem5065586 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term740 B s t x) = (term178 B s x t).
Proof. exact (eq_refl (term740 B s t x)). Qed.
Lemma lem5065587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5065588 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term741 B s t x) = (term735 B s x t).
Proof. exact (MK_COMB (@lem5065587) (@lem5065586 B s x t)). Qed.
Lemma lem5065589 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term741 B s t x) = (term736 B s x t).
Proof. exact (TRANS (@lem5065588 B s x t) (@lem5065578 B s x t)). Qed.
Lemma lem5065590 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term742 B s t) = (term743 B s t).
Proof. exact (fun_ext (fun x : B => @lem5065589 B s x t)). Qed.
Lemma lem5065591 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5065592 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term739 B s t) = (term744 B s t).
Proof. exact (MK_COMB (@lem5065591 B) (@lem5065590 B s t)). Qed.
Lemma lem5065593 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term738 B s t) = (term744 B s t).
Proof. exact (TRANS (@lem5065585 B s t) (@lem5065592 B s t)). Qed.
Lemma lem5065594 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term179 B s t) = (term745 B s t).
Proof. exact (fun_ext (fun x : B => @lem5065583 B s x t)). Qed.
Lemma lem5065595 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5065596 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term180 B s t) = (term746 B s t).
Proof. exact (MK_COMB (@lem5065595 B) (@lem5065594 B s t)). Qed.
Lemma lem5065598 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term747 B s t) = (term747 B s t).
Proof. exact (eq_refl (term747 B s t)). Qed.
Lemma lem5065599 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term748 B s t) = (term749 B s t).
Proof. exact (MK_COMB (@lem5065598 B s t) (@lem5065596 B s t)). Qed.
Lemma lem5065601 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term750 B s t) = (term750 B s t).
Proof. exact (eq_refl (term750 B s t)). Qed.
Lemma lem5065602 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term751 B s t) = (term752 B s t).
Proof. exact (MK_COMB (@lem5065601 B s t) (@lem5065593 B s t)). Qed.
Lemma lem5065603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065604 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term753 B s t) = (term754 B s t).
Proof. exact (MK_COMB (@lem5065603) (@lem5065602 B s t)). Qed.
Lemma lem5065605 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term755 B s t) = (term756 B s t).
Proof. exact (MK_COMB (@lem5065604 B s t) (@lem5065599 B s t)). Qed.
Lemma lem5065606 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term180 B s t)) = (term755 B s t).
Proof. exact (@lem17784 (@SUBSET B s t) (term180 B s t)). Qed.
Lemma lem5065607 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term180 B s t)) = (term756 B s t).
Proof. exact (TRANS (@lem5065606 B s t) (@lem5065605 B s t)). Qed.
Lemma lem5065608 {B : Type'} (s : B -> Prop) : (term182 B s) = (term757 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5065607 B s t)). Qed.
Lemma lem5065609 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065610 {B : Type'} (s : B -> Prop) : (term183 B s) = (term758 B s).
Proof. exact (MK_COMB (@lem5065609 B) (@lem5065608 B s)). Qed.
Lemma lem5065611 {B : Type'} : (term184 B) = (term759 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5065610 B s)). Qed.
Lemma lem5065612 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065613 {B : Type'} : (term148 B) = (term760 B).
Proof. exact (MK_COMB (@lem5065612 B) (@lem5065611 B)). Qed.
Lemma lem5065619 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5065620 {B : Type'} (P : type686 B) (Q : type686 B) : (term395 B P Q) = (term396 B P Q).
Proof. exact (@lem5065619 (B -> Prop) P Q). Qed.
Lemma lem5065621 {B : Type'} (s : B -> Prop) : (term761 B s) = (term762 B s).
Proof. exact (@lem5065620 B (term763 B s) (term764 B s)). Qed.
Lemma lem5065622 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term765 B s t) = (term752 B s t).
Proof. exact (eq_refl (term765 B s t)). Qed.
Lemma lem5065623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065624 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term766 B s t) = (term754 B s t).
Proof. exact (MK_COMB (@lem5065623) (@lem5065622 B s t)). Qed.
Lemma lem5065625 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term767 B s t) = (term749 B s t).
Proof. exact (eq_refl (term767 B s t)). Qed.
Lemma lem5065626 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term768 B s t) = (term756 B s t).
Proof. exact (MK_COMB (@lem5065624 B s t) (@lem5065625 B s t)). Qed.
Lemma lem5065627 {B : Type'} (s : B -> Prop) : (term769 B s) = (term757 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5065626 B s t)). Qed.
Lemma lem5065628 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065629 {B : Type'} (s : B -> Prop) : (term761 B s) = (term758 B s).
Proof. exact (MK_COMB (@lem5065628 B) (@lem5065627 B s)). Qed.
Lemma lem5065630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065631 {B : Type'} (s : B -> Prop) : (term770 B s) = (term771 B s).
Proof. exact (MK_COMB (@lem5065630) (@lem5065629 B s)). Qed.
Lemma lem5065632 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term765 B s t) = (term752 B s t).
Proof. exact (eq_refl (term765 B s t)). Qed.
Lemma lem5065633 {B : Type'} (s : B -> Prop) : (term772 B s) = (term763 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5065632 B s t)). Qed.
Lemma lem5065634 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065635 {B : Type'} (s : B -> Prop) : (term773 B s) = (term774 B s).
Proof. exact (MK_COMB (@lem5065634 B) (@lem5065633 B s)). Qed.
Lemma lem5065636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065637 {B : Type'} (s : B -> Prop) : (term775 B s) = (term776 B s).
Proof. exact (MK_COMB (@lem5065636) (@lem5065635 B s)). Qed.
Lemma lem5065638 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term767 B s t) = (term749 B s t).
Proof. exact (eq_refl (term767 B s t)). Qed.
Lemma lem5065639 {B : Type'} (s : B -> Prop) : (term777 B s) = (term764 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5065638 B s t)). Qed.
Lemma lem5065640 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065641 {B : Type'} (s : B -> Prop) : (term778 B s) = (term779 B s).
Proof. exact (MK_COMB (@lem5065640 B) (@lem5065639 B s)). Qed.
Lemma lem5065642 {B : Type'} (s : B -> Prop) : (term762 B s) = (term780 B s).
Proof. exact (MK_COMB (@lem5065637 B s) (@lem5065641 B s)). Qed.
Lemma lem5065643 {B : Type'} (s : B -> Prop) : ((term761 B s) = (term762 B s)) = ((term758 B s) = (term780 B s)).
Proof. exact (MK_COMB (@lem5065631 B s) (@lem5065642 B s)). Qed.
Lemma lem5065644 {B : Type'} (s : B -> Prop) : (term758 B s) = (term780 B s).
Proof. exact (EQ_MP (@lem5065643 B s) (@lem5065621 B s)). Qed.
Lemma lem5065837 {B : Type'} : (term759 B) = (term781 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5065644 B s)). Qed.
Lemma lem5065838 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065839 {B : Type'} : (term760 B) = (term782 B).
Proof. exact (MK_COMB (@lem5065838 B) (@lem5065837 B)). Qed.
Lemma lem5065841 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5065842 {B : Type'} (P : type686 B) (Q : type686 B) : (term395 B P Q) = (term396 B P Q).
Proof. exact (@lem5065841 (B -> Prop) P Q). Qed.
Lemma lem5065843 {B : Type'} : (term783 B) = (term784 B).
Proof. exact (@lem5065842 B (term785 B) (term786 B)). Qed.
Lemma lem5065844 {B : Type'} (s : B -> Prop) : (term787 B s) = (term774 B s).
Proof. exact (eq_refl (term787 B s)). Qed.
Lemma lem5065845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065846 {B : Type'} (s : B -> Prop) : (term788 B s) = (term776 B s).
Proof. exact (MK_COMB (@lem5065845) (@lem5065844 B s)). Qed.
Lemma lem5065847 {B : Type'} (s : B -> Prop) : (term789 B s) = (term779 B s).
Proof. exact (eq_refl (term789 B s)). Qed.
Lemma lem5065848 {B : Type'} (s : B -> Prop) : (term790 B s) = (term780 B s).
Proof. exact (MK_COMB (@lem5065846 B s) (@lem5065847 B s)). Qed.
Lemma lem5065849 {B : Type'} : (term791 B) = (term781 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5065848 B s)). Qed.
Lemma lem5065850 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065851 {B : Type'} : (term783 B) = (term782 B).
Proof. exact (MK_COMB (@lem5065850 B) (@lem5065849 B)). Qed.
Lemma lem5065852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5065853 {B : Type'} : (term792 B) = (term793 B).
Proof. exact (MK_COMB (@lem5065852) (@lem5065851 B)). Qed.
Lemma lem5065854 {B : Type'} (s : B -> Prop) : (term787 B s) = (term774 B s).
Proof. exact (eq_refl (term787 B s)). Qed.
Lemma lem5065855 {B : Type'} : (term794 B) = (term785 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5065854 B s)). Qed.
Lemma lem5065856 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065857 {B : Type'} : (term795 B) = (term796 B).
Proof. exact (MK_COMB (@lem5065856 B) (@lem5065855 B)). Qed.
Lemma lem5065858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5065859 {B : Type'} : (term797 B) = (term798 B).
Proof. exact (MK_COMB (@lem5065858) (@lem5065857 B)). Qed.
Lemma lem5065860 {B : Type'} (s : B -> Prop) : (term789 B s) = (term779 B s).
Proof. exact (eq_refl (term789 B s)). Qed.
Lemma lem5065861 {B : Type'} : (term799 B) = (term786 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5065860 B s)). Qed.
Lemma lem5065862 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5065863 {B : Type'} : (term800 B) = (term801 B).
Proof. exact (MK_COMB (@lem5065862 B) (@lem5065861 B)). Qed.
Lemma lem5065864 {B : Type'} : (term784 B) = (term802 B).
Proof. exact (MK_COMB (@lem5065859 B) (@lem5065863 B)). Qed.
Lemma lem5065865 {B : Type'} : ((term783 B) = (term784 B)) = ((term782 B) = (term802 B)).
Proof. exact (MK_COMB (@lem5065853 B) (@lem5065864 B)). Qed.
Lemma lem5065866 {B : Type'} : (term782 B) = (term802 B).
Proof. exact (EQ_MP (@lem5065865 B) (@lem5065843 B)). Qed.
Lemma lem5066067 {B : Type'} : (term760 B) = (term802 B).
Proof. exact (TRANS (@lem5065839 B) (@lem5065866 B)). Qed.
Lemma lem5066069 {A : Type'} (P : Prop) (Q : A -> Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5066070 {B : Type'} (P : Prop) (Q : B -> Prop) : (term296 B P Q) = (term297 B P Q).
Proof. exact (@lem5066069 B P Q). Qed.
Lemma lem5066071 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term803 B s t) = (term804 B s t).
Proof. exact (@lem5066070 B (@SUBSET B s t) (term743 B s t)). Qed.
Lemma lem5066072 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term805 B s t x) = (term736 B s x t).
Proof. exact (eq_refl (term805 B s t x)). Qed.
Lemma lem5066073 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term806 B s t) = (term743 B s t).
Proof. exact (fun_ext (fun x : B => @lem5066072 B s x t)). Qed.
Lemma lem5066074 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5066075 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term807 B s t) = (term744 B s t).
Proof. exact (MK_COMB (@lem5066074 B) (@lem5066073 B s t)). Qed.
Lemma lem5066076 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term750 B s t) = (term750 B s t).
Proof. exact (eq_refl (term750 B s t)). Qed.
Lemma lem5066077 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term803 B s t) = (term752 B s t).
Proof. exact (MK_COMB (@lem5066076 B s t) (@lem5066075 B s t)). Qed.
Lemma lem5066078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5066079 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term808 B s t) = (term809 B s t).
Proof. exact (MK_COMB (@lem5066078) (@lem5066077 B s t)). Qed.
Lemma lem5066080 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term805 B s t x) = (term736 B s x t).
Proof. exact (eq_refl (term805 B s t x)). Qed.
Lemma lem5066081 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term750 B s t) = (term750 B s t).
Proof. exact (eq_refl (term750 B s t)). Qed.
Lemma lem5066082 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term810 B s t x) = (term811 B s x t).
Proof. exact (MK_COMB (@lem5066081 B s t) (@lem5066080 B s x t)). Qed.
Lemma lem5066083 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term812 B s t) = (term813 B s t).
Proof. exact (fun_ext (fun x : B => @lem5066082 B s x t)). Qed.
Lemma lem5066084 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5066085 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term804 B s t) = (term814 B s t).
Proof. exact (MK_COMB (@lem5066084 B) (@lem5066083 B s t)). Qed.
Lemma lem5066086 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term803 B s t) = (term804 B s t)) = ((term752 B s t) = (term814 B s t)).
Proof. exact (MK_COMB (@lem5066079 B s t) (@lem5066085 B s t)). Qed.
Lemma lem5066087 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term752 B s t) = (term814 B s t).
Proof. exact (EQ_MP (@lem5066086 B s t) (@lem5066071 B s t)). Qed.
Lemma lem5066088 {B : Type'} (s : B -> Prop) : (term763 B s) = (term815 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5066087 B s t)). Qed.
Lemma lem5066089 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066090 {B : Type'} (s : B -> Prop) : (term774 B s) = (term816 B s).
Proof. exact (MK_COMB (@lem5066089 B) (@lem5066088 B s)). Qed.
Lemma lem5066092 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5066093 {B : Type'} (P : type672 B) : (term817 B P) = (term818 B P).
Proof. exact (@lem5066092 (B -> Prop) B P). Qed.
Lemma lem5066094 {B : Type'} (s : B -> Prop) : (term819 B s) = (term820 B s).
Proof. exact (@lem5066093 B (term821 B s)). Qed.
Lemma lem5066095 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term822 B s t) = (term813 B s t).
Proof. exact (eq_refl (term822 B s t)). Qed.
Lemma lem5066096 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5066097 {B : Type'} (s : B -> Prop) (t : B -> Prop) (x : B) : (term823 B s t x) = (term824 B s t x).
Proof. exact (MK_COMB (@lem5066095 B s t) (@lem5066096 B x)). Qed.
Lemma lem5066098 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term824 B s t x) = (term811 B s x t).
Proof. exact (eq_refl (term824 B s t x)). Qed.
Lemma lem5066099 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term823 B s t x) = (term811 B s x t).
Proof. exact (TRANS (@lem5066097 B s t x) (@lem5066098 B s x t)). Qed.
Lemma lem5066100 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term825 B s t) = (term813 B s t).
Proof. exact (fun_ext (fun x : B => @lem5066099 B s x t)). Qed.
Lemma lem5066101 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5066102 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term826 B s t) = (term814 B s t).
Proof. exact (MK_COMB (@lem5066101 B) (@lem5066100 B s t)). Qed.
Lemma lem5066103 {B : Type'} (s : B -> Prop) : (term827 B s) = (term815 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5066102 B s t)). Qed.
Lemma lem5066104 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066105 {B : Type'} (s : B -> Prop) : (term819 B s) = (term816 B s).
Proof. exact (MK_COMB (@lem5066104 B) (@lem5066103 B s)). Qed.
Lemma lem5066106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5066107 {B : Type'} (s : B -> Prop) : (term828 B s) = (term829 B s).
Proof. exact (MK_COMB (@lem5066106) (@lem5066105 B s)). Qed.
Lemma lem5066108 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term822 B s t) = (term813 B s t).
Proof. exact (eq_refl (term822 B s t)). Qed.
Lemma lem5066109 {B : Type'} (x : type684 B) (t : B -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem5066110 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term830 B s x t) = (term831 B s x t).
Proof. exact (MK_COMB (@lem5066108 B s t) (@lem5066109 B x t)). Qed.
Lemma lem5066111 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term831 B s x t) = (term832 B s x t).
Proof. exact (eq_refl (term831 B s x t)). Qed.
Lemma lem5066112 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term830 B s x t) = (term832 B s x t).
Proof. exact (TRANS (@lem5066110 B s x t) (@lem5066111 B s x t)). Qed.
Lemma lem5066113 {B : Type'} (s : B -> Prop) (x : type684 B) : (term833 B s x) = (term834 B s x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5066112 B s x t)). Qed.
Lemma lem5066114 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066115 {B : Type'} (s : B -> Prop) (x : type684 B) : (term835 B s x) = (term836 B s x).
Proof. exact (MK_COMB (@lem5066114 B) (@lem5066113 B s x)). Qed.
Lemma lem5066116 {B : Type'} (s : B -> Prop) : (term837 B s) = (term838 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem5066115 B s x)). Qed.
Lemma lem5066117 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5066118 {B : Type'} (s : B -> Prop) : (term820 B s) = (term839 B s).
Proof. exact (MK_COMB (@lem5066117 B) (@lem5066116 B s)). Qed.
Lemma lem5066119 {B : Type'} (s : B -> Prop) : ((term819 B s) = (term820 B s)) = ((term816 B s) = (term839 B s)).
Proof. exact (MK_COMB (@lem5066107 B s) (@lem5066118 B s)). Qed.
Lemma lem5066120 {B : Type'} (s : B -> Prop) : (term816 B s) = (term839 B s).
Proof. exact (EQ_MP (@lem5066119 B s) (@lem5066094 B s)). Qed.
Lemma lem5066121 {B : Type'} (s : B -> Prop) : (term774 B s) = (term839 B s).
Proof. exact (TRANS (@lem5066090 B s) (@lem5066120 B s)). Qed.
Lemma lem5066122 {B : Type'} : (term785 B) = (term840 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5066121 B s)). Qed.
Lemma lem5066123 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066124 {B : Type'} : (term796 B) = (term841 B).
Proof. exact (MK_COMB (@lem5066123 B) (@lem5066122 B)). Qed.
Lemma lem5066126 {A B : Type'} (P : type1413 A B) : (term453 A B P) = (term454 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5066127 {B : Type'} (P : type597 B) : (term842 B P) = (term843 B P).
Proof. exact (@lem5066126 (B -> Prop) (type684 B) P). Qed.
Lemma lem5066128 {B : Type'} : (term844 B) = (term845 B).
Proof. exact (@lem5066127 B (term846 B)). Qed.
Lemma lem5066129 {B : Type'} (s : B -> Prop) : (term847 B s) = (term838 B s).
Proof. exact (eq_refl (term847 B s)). Qed.
Lemma lem5066130 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5066131 {B : Type'} (s : B -> Prop) (x : type684 B) : (term848 B s x) = (term849 B s x).
Proof. exact (MK_COMB (@lem5066129 B s) (@lem5066130 B x)). Qed.
Lemma lem5066132 {B : Type'} (s : B -> Prop) (x : type684 B) : (term849 B s x) = (term836 B s x).
Proof. exact (eq_refl (term849 B s x)). Qed.
Lemma lem5066133 {B : Type'} (s : B -> Prop) (x : type684 B) : (term848 B s x) = (term836 B s x).
Proof. exact (TRANS (@lem5066131 B s x) (@lem5066132 B s x)). Qed.
Lemma lem5066134 {B : Type'} (s : B -> Prop) : (term850 B s) = (term838 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem5066133 B s x)). Qed.
Lemma lem5066135 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5066136 {B : Type'} (s : B -> Prop) : (term851 B s) = (term839 B s).
Proof. exact (MK_COMB (@lem5066135 B) (@lem5066134 B s)). Qed.
Lemma lem5066137 {B : Type'} : (term852 B) = (term840 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5066136 B s)). Qed.
Lemma lem5066138 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066139 {B : Type'} : (term844 B) = (term841 B).
Proof. exact (MK_COMB (@lem5066138 B) (@lem5066137 B)). Qed.
Lemma lem5066140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5066141 {B : Type'} : (term853 B) = (term854 B).
Proof. exact (MK_COMB (@lem5066140) (@lem5066139 B)). Qed.
Lemma lem5066142 {B : Type'} (s : B -> Prop) : (term847 B s) = (term838 B s).
Proof. exact (eq_refl (term847 B s)). Qed.
Lemma lem5066143 {B : Type'} (x : type638 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5066144 {B : Type'} (x : type638 B) (s : B -> Prop) : (term855 B x s) = (term856 B x s).
Proof. exact (MK_COMB (@lem5066142 B s) (@lem5066143 B x s)). Qed.
Lemma lem5066145 {B : Type'} (x : type638 B) (s : B -> Prop) : (term856 B x s) = (term857 B x s).
Proof. exact (eq_refl (term856 B x s)). Qed.
Lemma lem5066146 {B : Type'} (x : type638 B) (s : B -> Prop) : (term855 B x s) = (term857 B x s).
Proof. exact (TRANS (@lem5066144 B x s) (@lem5066145 B x s)). Qed.
Lemma lem5066147 {B : Type'} (x : type638 B) : (term858 B x) = (term859 B x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5066146 B x s)). Qed.
Lemma lem5066148 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066149 {B : Type'} (x : type638 B) : (term860 B x) = (term861 B x).
Proof. exact (MK_COMB (@lem5066148 B) (@lem5066147 B x)). Qed.
Lemma lem5066150 {B : Type'} : (term862 B) = (term863 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5066149 B x)). Qed.
Lemma lem5066151 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5066152 {B : Type'} : (term845 B) = (term864 B).
Proof. exact (MK_COMB (@lem5066151 B) (@lem5066150 B)). Qed.
Lemma lem5066153 {B : Type'} : ((term844 B) = (term845 B)) = ((term841 B) = (term864 B)).
Proof. exact (MK_COMB (@lem5066141 B) (@lem5066152 B)). Qed.
Lemma lem5066154 {B : Type'} : (term841 B) = (term864 B).
Proof. exact (EQ_MP (@lem5066153 B) (@lem5066128 B)). Qed.
Lemma lem5066155 {B : Type'} : (term796 B) = (term864 B).
Proof. exact (TRANS (@lem5066124 B) (@lem5066154 B)). Qed.
Lemma lem5066156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066157 {B : Type'} : (term798 B) = (term865 B).
Proof. exact (MK_COMB (@lem5066156) (@lem5066155 B)). Qed.
Lemma lem5066158 {B : Type'} : (term801 B) = (term801 B).
Proof. exact (eq_refl (term801 B)). Qed.
Lemma lem5066159 {B : Type'} : (term802 B) = (term866 B).
Proof. exact (MK_COMB (@lem5066157 B) (@lem5066158 B)). Qed.
Lemma lem5066161 {A : Type'} (P : A -> Prop) (Q : Prop) : (term867 A P Q) = (term868 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5066162 {B : Type'} (P : type139 B) (Q : Prop) : (term869 B P Q) = (term870 B P Q).
Proof. exact (@lem5066161 (type638 B) P Q). Qed.
Lemma lem5066163 {B : Type'} : (term871 B) = (term872 B).
Proof. exact (@lem5066162 B (term863 B) (term801 B)). Qed.
Lemma lem5066164 {B : Type'} (x : type638 B) : (term873 B x) = (term861 B x).
Proof. exact (eq_refl (term873 B x)). Qed.
Lemma lem5066165 {B : Type'} : (term874 B) = (term863 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5066164 B x)). Qed.
Lemma lem5066166 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5066167 {B : Type'} : (term875 B) = (term864 B).
Proof. exact (MK_COMB (@lem5066166 B) (@lem5066165 B)). Qed.
Lemma lem5066168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066169 {B : Type'} : (term876 B) = (term865 B).
Proof. exact (MK_COMB (@lem5066168) (@lem5066167 B)). Qed.
Lemma lem5066170 {B : Type'} : (term801 B) = (term801 B).
Proof. exact (eq_refl (term801 B)). Qed.
Lemma lem5066171 {B : Type'} : (term871 B) = (term866 B).
Proof. exact (MK_COMB (@lem5066169 B) (@lem5066170 B)). Qed.
Lemma lem5066172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5066173 {B : Type'} : (term877 B) = (term878 B).
Proof. exact (MK_COMB (@lem5066172) (@lem5066171 B)). Qed.
Lemma lem5066174 {B : Type'} (x : type638 B) : (term873 B x) = (term861 B x).
Proof. exact (eq_refl (term873 B x)). Qed.
Lemma lem5066175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066176 {B : Type'} (x : type638 B) : (term879 B x) = (term880 B x).
Proof. exact (MK_COMB (@lem5066175) (@lem5066174 B x)). Qed.
Lemma lem5066177 {B : Type'} : (term801 B) = (term801 B).
Proof. exact (eq_refl (term801 B)). Qed.
Lemma lem5066178 {B : Type'} (x : type638 B) : (term881 B x) = (term882 B x).
Proof. exact (MK_COMB (@lem5066176 B x) (@lem5066177 B)). Qed.
Lemma lem5066179 {B : Type'} : (term883 B) = (term884 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5066178 B x)). Qed.
Lemma lem5066180 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5066181 {B : Type'} : (term872 B) = (term885 B).
Proof. exact (MK_COMB (@lem5066180 B) (@lem5066179 B)). Qed.
Lemma lem5066182 {B : Type'} : ((term871 B) = (term872 B)) = ((term866 B) = (term885 B)).
Proof. exact (MK_COMB (@lem5066173 B) (@lem5066181 B)). Qed.
Lemma lem5066183 {B : Type'} : (term866 B) = (term885 B).
Proof. exact (EQ_MP (@lem5066182 B) (@lem5066163 B)). Qed.
Lemma lem5066184 {B : Type'} : (term802 B) = (term885 B).
Proof. exact (TRANS (@lem5066159 B) (@lem5066183 B)). Qed.
Lemma lem5066185 {B : Type'} : (term760 B) = (term885 B).
Proof. exact (TRANS (@lem5066067 B) (@lem5066184 B)). Qed.
Lemma lem5066186 {B : Type'} : (term148 B) = (term885 B).
Proof. exact (TRANS (@lem5065613 B) (@lem5066185 B)). Qed.
Lemma lem5066187 {B : Type'} (h1 : term148 B) : term885 B.
Proof. exact (EQ_MP (@lem5066186 B) (@lem5061865 B h1)). Qed.
Lemma lem5066188 {B : Type'} (x : type638 B) (h1 : term882 B x) : term882 B x.
Proof. exact (h1). Qed.
Lemma lem5066191 {A B : Type'} (x''' : type1448 A B) (h1 : term731 A B x''') : term731 A B x'''.
Proof. exact (h1). Qed.
Lemma lem5066193 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term340 A B t s f) : term340 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5066194 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (h1 : term338 A B t s f x''''') : term338 A B t s f x'''''.
Proof. exact (h1). Qed.
Lemma lem5066195 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term335 A B t s f x''''' y.
Proof. exact (h1). Qed.
Lemma lem5066202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066203 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066202 B (type686 B) f x). Qed.
Lemma lem5066204 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem5066203 B (@IN B) x). Qed.
Lemma lem5066205 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066206 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x t).
Proof. exact (MK_COMB (@lem5066204 B x) (@lem5066205 B t)). Qed.
Lemma lem5066208 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066209 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066208 (B -> Prop) Prop f x). Qed.
Lemma lem5066210 {B : Type'} (x : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x t) = (term886 B x t).
Proof. exact (@lem5066209 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) t). Qed.
Lemma lem5066212 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (term886 B x t).
Proof. exact (TRANS (@lem5066206 B x t) (@lem5066210 B x t)). Qed.
Lemma lem5066213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066221 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066220 B (type686 B) f x). Qed.
Lemma lem5066222 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem5066221 B (@IN B) x). Qed.
Lemma lem5066223 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066224 {B : Type'} (x : B) (s : B -> Prop) : (@IN B x s) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x s).
Proof. exact (MK_COMB (@lem5066222 B x) (@lem5066223 B s)). Qed.
Lemma lem5066226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066227 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066226 (B -> Prop) Prop f x). Qed.
Lemma lem5066228 {B : Type'} (x : B) (s : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x s) = (term886 B x s).
Proof. exact (@lem5066227 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) s). Qed.
Lemma lem5066230 {B : Type'} (x : B) (s : B -> Prop) : (@IN B x s) = (term886 B x s).
Proof. exact (TRANS (@lem5066224 B x s) (@lem5066228 B x s)). Qed.
Lemma lem5066231 {B : Type'} (x : B) (s : B -> Prop) : (term887 B x s) = (term888 B x s).
Proof. exact (MK_COMB (@lem5066213) (@lem5066230 B x s)). Qed.
Lemma lem5066232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066233 {B : Type'} (x : B) (s : B -> Prop) : (term215 B x s) = (term889 B x s).
Proof. exact (MK_COMB (@lem5066232) (@lem5066231 B x s)). Qed.
Lemma lem5066234 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term737 B s x t) = (term890 B s x t).
Proof. exact (MK_COMB (@lem5066233 B x s) (@lem5066212 B x t)). Qed.
Lemma lem5066235 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term745 B s t) = (term891 B s t).
Proof. exact (fun_ext (fun x : B => @lem5066234 B s x t)). Qed.
Lemma lem5066236 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5066237 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term746 B s t) = (term892 B s t).
Proof. exact (MK_COMB (@lem5066236 B) (@lem5066235 B s t)). Qed.
Lemma lem5066238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066246 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066245 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5066247 {B : Type'} (s : B -> Prop) : (@SUBSET B s) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s).
Proof. exact (@lem5066246 B (@SUBSET B) s). Qed.
Lemma lem5066248 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066249 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t).
Proof. exact (MK_COMB (@lem5066247 B s) (@lem5066248 B t)). Qed.
Lemma lem5066251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066252 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066251 (B -> Prop) Prop f x). Qed.
Lemma lem5066253 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t) = (term893 B s t).
Proof. exact (@lem5066252 B (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s) t). Qed.
Lemma lem5066255 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term893 B s t).
Proof. exact (TRANS (@lem5066249 B s t) (@lem5066253 B s t)). Qed.
Lemma lem5066256 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term894 B s t) = (term895 B s t).
Proof. exact (MK_COMB (@lem5066238) (@lem5066255 B s t)). Qed.
Lemma lem5066257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066258 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term747 B s t) = (term896 B s t).
Proof. exact (MK_COMB (@lem5066257) (@lem5066256 B s t)). Qed.
Lemma lem5066259 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term749 B s t) = (term897 B s t).
Proof. exact (MK_COMB (@lem5066258 B s t) (@lem5066237 B s t)). Qed.
Lemma lem5066260 {B : Type'} (s : B -> Prop) : (term764 B s) = (term898 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5066259 B s t)). Qed.
Lemma lem5066261 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066262 {B : Type'} (s : B -> Prop) : (term779 B s) = (term899 B s).
Proof. exact (MK_COMB (@lem5066261 B) (@lem5066260 B s)). Qed.
Lemma lem5066263 {B : Type'} : (term786 B) = (term900 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5066262 B s)). Qed.
Lemma lem5066264 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066265 {B : Type'} : (term801 B) = (term901 B).
Proof. exact (MK_COMB (@lem5066264 B) (@lem5066263 B)). Qed.
Lemma lem5066266 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066267 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5066274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066275 {B : Type'} (f : type638 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> B) f x).
Proof. exact (@lem5066274 (B -> Prop) (type684 B) f x). Qed.
Lemma lem5066276 {B : Type'} (x : type638 B) (s : B -> Prop) : (x s) = (@I ((B -> Prop) -> (B -> Prop) -> B) x s).
Proof. exact (@lem5066275 B x s). Qed.
Lemma lem5066277 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066278 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (x s t) = (@I ((B -> Prop) -> (B -> Prop) -> B) x s t).
Proof. exact (MK_COMB (@lem5066276 B x s) (@lem5066277 B t)). Qed.
Lemma lem5066280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066281 {B : Type'} (f : type684 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> B) f x).
Proof. exact (@lem5066280 (B -> Prop) B f x). Qed.
Lemma lem5066282 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> B) x s t) = (term902 B x s t).
Proof. exact (@lem5066281 B (@I ((B -> Prop) -> (B -> Prop) -> B) x s) t). Qed.
Lemma lem5066284 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (x s t) = (term902 B x s t).
Proof. exact (TRANS (@lem5066278 B x s t) (@lem5066282 B x s t)). Qed.
Lemma lem5066285 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066286 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term903 B x s t) = (term904 B x s t).
Proof. exact (MK_COMB (@lem5066267 B) (@lem5066284 B x s t)). Qed.
Lemma lem5066287 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term905 B x s t) = (term906 B x s t).
Proof. exact (MK_COMB (@lem5066286 B x s t) (@lem5066285 B t)). Qed.
Lemma lem5066289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066290 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066289 B (type686 B) f x). Qed.
Lemma lem5066291 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term904 B x s t) = (term907 B x s t).
Proof. exact (@lem5066290 B (@IN B) (term902 B x s t)). Qed.
Lemma lem5066292 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066293 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term906 B x s t) = (term908 B x s t).
Proof. exact (MK_COMB (@lem5066291 B x s t) (@lem5066292 B t)). Qed.
Lemma lem5066295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066296 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066295 (B -> Prop) Prop f x). Qed.
Lemma lem5066297 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term908 B x s t) = (term909 B x s t).
Proof. exact (@lem5066296 B (term907 B x s t) t). Qed.
Lemma lem5066298 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term906 B x s t) = (term909 B x s t).
Proof. exact (TRANS (@lem5066293 B x s t) (@lem5066297 B x s t)). Qed.
Lemma lem5066299 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term905 B x s t) = (term909 B x s t).
Proof. exact (TRANS (@lem5066287 B x s t) (@lem5066298 B x s t)). Qed.
Lemma lem5066300 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term910 B x s t) = (term911 B x s t).
Proof. exact (MK_COMB (@lem5066266) (@lem5066299 B x s t)). Qed.
Lemma lem5066301 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5066308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066309 {B : Type'} (f : type638 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> B) f x).
Proof. exact (@lem5066308 (B -> Prop) (type684 B) f x). Qed.
Lemma lem5066310 {B : Type'} (x : type638 B) (s : B -> Prop) : (x s) = (@I ((B -> Prop) -> (B -> Prop) -> B) x s).
Proof. exact (@lem5066309 B x s). Qed.
Lemma lem5066311 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066312 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (x s t) = (@I ((B -> Prop) -> (B -> Prop) -> B) x s t).
Proof. exact (MK_COMB (@lem5066310 B x s) (@lem5066311 B t)). Qed.
Lemma lem5066314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066315 {B : Type'} (f : type684 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> B) f x).
Proof. exact (@lem5066314 (B -> Prop) B f x). Qed.
Lemma lem5066316 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> B) x s t) = (term902 B x s t).
Proof. exact (@lem5066315 B (@I ((B -> Prop) -> (B -> Prop) -> B) x s) t). Qed.
Lemma lem5066318 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (x s t) = (term902 B x s t).
Proof. exact (TRANS (@lem5066312 B x s t) (@lem5066316 B x s t)). Qed.
Lemma lem5066319 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066320 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term903 B x s t) = (term904 B x s t).
Proof. exact (MK_COMB (@lem5066301 B) (@lem5066318 B x s t)). Qed.
Lemma lem5066321 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term912 B x t s) = (term913 B x t s).
Proof. exact (MK_COMB (@lem5066320 B x s t) (@lem5066319 B s)). Qed.
Lemma lem5066323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066324 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066323 B (type686 B) f x). Qed.
Lemma lem5066325 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term904 B x s t) = (term907 B x s t).
Proof. exact (@lem5066324 B (@IN B) (term902 B x s t)). Qed.
Lemma lem5066326 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066327 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term913 B x t s) = (term914 B x t s).
Proof. exact (MK_COMB (@lem5066325 B x s t) (@lem5066326 B s)). Qed.
Lemma lem5066329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066330 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066329 (B -> Prop) Prop f x). Qed.
Lemma lem5066331 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term914 B x t s) = (term915 B x t s).
Proof. exact (@lem5066330 B (term907 B x s t) s). Qed.
Lemma lem5066332 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term913 B x t s) = (term915 B x t s).
Proof. exact (TRANS (@lem5066327 B x t s) (@lem5066331 B x t s)). Qed.
Lemma lem5066333 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term912 B x t s) = (term915 B x t s).
Proof. exact (TRANS (@lem5066321 B x t s) (@lem5066332 B x t s)). Qed.
Lemma lem5066334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066335 {B : Type'} (x : type638 B) (t : B -> Prop) (s : B -> Prop) : (term916 B x t s) = (term917 B x t s).
Proof. exact (MK_COMB (@lem5066334) (@lem5066333 B x t s)). Qed.
Lemma lem5066336 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term918 B x s t) = (term919 B x s t).
Proof. exact (MK_COMB (@lem5066335 B x t s) (@lem5066300 B x s t)). Qed.
Lemma lem5066343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066344 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066343 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5066345 {B : Type'} (s : B -> Prop) : (@SUBSET B s) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s).
Proof. exact (@lem5066344 B (@SUBSET B) s). Qed.
Lemma lem5066346 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5066347 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t).
Proof. exact (MK_COMB (@lem5066345 B s) (@lem5066346 B t)). Qed.
Lemma lem5066349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066350 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066349 (B -> Prop) Prop f x). Qed.
Lemma lem5066351 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t) = (term893 B s t).
Proof. exact (@lem5066350 B (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s) t). Qed.
Lemma lem5066353 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term893 B s t).
Proof. exact (TRANS (@lem5066347 B s t) (@lem5066351 B s t)). Qed.
Lemma lem5066354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066355 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term750 B s t) = (term920 B s t).
Proof. exact (MK_COMB (@lem5066354) (@lem5066353 B s t)). Qed.
Lemma lem5066356 {B : Type'} (x : type638 B) (s : B -> Prop) (t : B -> Prop) : (term921 B x s t) = (term922 B x s t).
Proof. exact (MK_COMB (@lem5066355 B s t) (@lem5066336 B x s t)). Qed.
Lemma lem5066357 {B : Type'} (x : type638 B) (s : B -> Prop) : (term923 B x s) = (term924 B x s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5066356 B x s t)). Qed.
Lemma lem5066358 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066359 {B : Type'} (x : type638 B) (s : B -> Prop) : (term857 B x s) = (term925 B x s).
Proof. exact (MK_COMB (@lem5066358 B) (@lem5066357 B x s)). Qed.
Lemma lem5066360 {B : Type'} (x : type638 B) : (term859 B x) = (term926 B x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5066359 B x s)). Qed.
Lemma lem5066361 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5066362 {B : Type'} (x : type638 B) : (term861 B x) = (term927 B x).
Proof. exact (MK_COMB (@lem5066361 B) (@lem5066360 B x)). Qed.
Lemma lem5066363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066364 {B : Type'} (x : type638 B) : (term880 B x) = (term928 B x).
Proof. exact (MK_COMB (@lem5066363) (@lem5066362 B x)). Qed.
Lemma lem5066365 {B : Type'} (x : type638 B) : (term882 B x) = (term929 B x).
Proof. exact (MK_COMB (@lem5066364 B x) (@lem5066265 B)). Qed.
Lemma lem5066366 {B : Type'} (x : type638 B) (h1 : term882 B x) : term929 B x.
Proof. exact (EQ_MP (@lem5066365 B x) (@lem5066188 B x h1)). Qed.
Lemma lem5066754 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5066763 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066764 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5066763 B (type631 A B) f x). Qed.
Lemma lem5066765 {A B : Type'} (x''' : type1448 A B) (y : B) : (x''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y).
Proof. exact (@lem5066764 A B x''' y). Qed.
Lemma lem5066766 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066767 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (x''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y s).
Proof. exact (MK_COMB (@lem5066765 A B x''' y) (@lem5066766 A s)). Qed.
Lemma lem5066769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066770 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5066769 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem5066771 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y s) = (term930 A B x''' y s).
Proof. exact (@lem5066770 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y) s). Qed.
Lemma lem5066772 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (x''' y s) = (term930 A B x''' y s).
Proof. exact (TRANS (@lem5066767 A B x''' y s) (@lem5066771 A B x''' y s)). Qed.
Lemma lem5066773 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5066774 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x''' y s f) = (term931 A B x''' y s f).
Proof. exact (MK_COMB (@lem5066772 A B x''' y s) (@lem5066773 A B f)). Qed.
Lemma lem5066776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066777 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem5066776 (A -> B) A f x). Qed.
Lemma lem5066778 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term931 A B x''' y s f) = (term932 A B x''' y s f).
Proof. exact (@lem5066777 A B (term930 A B x''' y s) f). Qed.
Lemma lem5066780 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x''' y s f) = (term932 A B x''' y s f).
Proof. exact (TRANS (@lem5066774 A B x''' y s f) (@lem5066778 A B x''' y s f)). Qed.
Lemma lem5066781 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066782 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term933 A B x''' y s f) = (term934 A B x''' y s f).
Proof. exact (MK_COMB (@lem5066754 A) (@lem5066780 A B x''' y s f)). Qed.
Lemma lem5066783 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term935 A B x''' y f s) = (term936 A B x''' y f s).
Proof. exact (MK_COMB (@lem5066782 A B x''' y s f) (@lem5066781 A s)). Qed.
Lemma lem5066785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066786 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5066785 A (type686 A) f x). Qed.
Lemma lem5066787 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term934 A B x''' y s f) = (term937 A B x''' y s f).
Proof. exact (@lem5066786 A (@IN A) (term932 A B x''' y s f)). Qed.
Lemma lem5066788 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066789 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term936 A B x''' y f s) = (term938 A B x''' y f s).
Proof. exact (MK_COMB (@lem5066787 A B x''' y s f) (@lem5066788 A s)). Qed.
Lemma lem5066791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066792 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5066791 (A -> Prop) Prop f x). Qed.
Lemma lem5066793 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term938 A B x''' y f s) = (term939 A B x''' y f s).
Proof. exact (@lem5066792 A (term937 A B x''' y s f) s). Qed.
Lemma lem5066794 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term936 A B x''' y f s) = (term939 A B x''' y f s).
Proof. exact (TRANS (@lem5066789 A B x''' y f s) (@lem5066793 A B x''' y f s)). Qed.
Lemma lem5066795 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term935 A B x''' y f s) = (term939 A B x''' y f s).
Proof. exact (TRANS (@lem5066783 A B x''' y f s) (@lem5066794 A B x''' y f s)). Qed.
Lemma lem5066798 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5066807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066808 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5066807 B (type631 A B) f x). Qed.
Lemma lem5066809 {A B : Type'} (x''' : type1448 A B) (y : B) : (x''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y).
Proof. exact (@lem5066808 A B x''' y). Qed.
Lemma lem5066810 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066811 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (x''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y s).
Proof. exact (MK_COMB (@lem5066809 A B x''' y) (@lem5066810 A s)). Qed.
Lemma lem5066813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066814 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5066813 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem5066815 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y s) = (term930 A B x''' y s).
Proof. exact (@lem5066814 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x''' y) s). Qed.
Lemma lem5066816 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (x''' y s) = (term930 A B x''' y s).
Proof. exact (TRANS (@lem5066811 A B x''' y s) (@lem5066815 A B x''' y s)). Qed.
Lemma lem5066817 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5066818 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x''' y s f) = (term931 A B x''' y s f).
Proof. exact (MK_COMB (@lem5066816 A B x''' y s) (@lem5066817 A B f)). Qed.
Lemma lem5066820 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066821 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem5066820 (A -> B) A f x). Qed.
Lemma lem5066822 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term931 A B x''' y s f) = (term932 A B x''' y s f).
Proof. exact (@lem5066821 A B (term930 A B x''' y s) f). Qed.
Lemma lem5066824 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x''' y s f) = (term932 A B x''' y s f).
Proof. exact (TRANS (@lem5066818 A B x''' y s f) (@lem5066822 A B x''' y s f)). Qed.
Lemma lem5066825 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term940 A B x''' y s f) = (term941 A B x''' y s f).
Proof. exact (MK_COMB (@lem5066798 A B f) (@lem5066824 A B x''' y s f)). Qed.
Lemma lem5066827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066828 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5066827 A B f x). Qed.
Lemma lem5066829 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term941 A B x''' y s f) = (term942 A B x''' y s f).
Proof. exact (@lem5066828 A B f (term932 A B x''' y s f)). Qed.
Lemma lem5066830 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term940 A B x''' y s f) = (term942 A B x''' y s f).
Proof. exact (TRANS (@lem5066825 A B x''' y s f) (@lem5066829 A B x''' y s f)). Qed.
Lemma lem5066831 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5066832 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (y = (term940 A B x''' y s f)) = (y = (term942 A B x''' y s f)).
Proof. exact (MK_COMB (@lem5066831 B y) (@lem5066830 A B x''' y s f)). Qed.
Lemma lem5066833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066834 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term943 A B x''' y s f) = (term944 A B x''' y s f).
Proof. exact (MK_COMB (@lem5066833) (@lem5066832 A B x''' y s f)). Qed.
Lemma lem5066835 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term945 A B x''' y f s) = (term946 A B x''' y f s).
Proof. exact (MK_COMB (@lem5066834 A B x''' y s f) (@lem5066795 A B x''' y f s)). Qed.
Lemma lem5066836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066846 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5066845 (A -> B) (type678 A B) f x). Qed.
Lemma lem5066847 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5066846 A B (@IMAGE A B) f). Qed.
Lemma lem5066848 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066849 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5066847 A B f) (@lem5066848 A s)). Qed.
Lemma lem5066851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066852 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5066851 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5066853 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term947 A B f s).
Proof. exact (@lem5066852 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5066855 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term947 A B f s).
Proof. exact (TRANS (@lem5066849 A B f s) (@lem5066853 A B f s)). Qed.
Lemma lem5066856 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem5066857 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term199 A B y f s) = (term948 A B y f s).
Proof. exact (MK_COMB (@lem5066856 B y) (@lem5066855 A B f s)). Qed.
Lemma lem5066859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066860 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066859 B (type686 B) f x). Qed.
Lemma lem5066861 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem5066860 B (@IN B) y). Qed.
Lemma lem5066862 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term947 A B f s) = (term947 A B f s).
Proof. exact (eq_refl (term947 A B f s)). Qed.
Lemma lem5066863 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term949 A B y f s).
Proof. exact (MK_COMB (@lem5066861 B y) (@lem5066862 A B f s)). Qed.
Lemma lem5066865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066866 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066865 (B -> Prop) Prop f x). Qed.
Lemma lem5066867 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term949 A B y f s) = (term950 A B y f s).
Proof. exact (@lem5066866 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term947 A B f s)). Qed.
Lemma lem5066868 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term950 A B y f s).
Proof. exact (TRANS (@lem5066863 A B y f s) (@lem5066867 A B y f s)). Qed.
Lemma lem5066869 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term199 A B y f s) = (term950 A B y f s).
Proof. exact (TRANS (@lem5066857 A B y f s) (@lem5066868 A B y f s)). Qed.
Lemma lem5066870 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term635 A B y f s) = (term951 A B y f s).
Proof. exact (MK_COMB (@lem5066836) (@lem5066869 A B y f s)). Qed.
Lemma lem5066871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066872 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term552 A B y f s) = (term952 A B y f s).
Proof. exact (MK_COMB (@lem5066871) (@lem5066870 A B y f s)). Qed.
Lemma lem5066873 {A B : Type'} (x''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term953 A B x''' y f s) = (term954 A B x''' y f s).
Proof. exact (MK_COMB (@lem5066872 A B y f s) (@lem5066835 A B x''' y f s)). Qed.
Lemma lem5066874 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (term955 A B x''' y s) = (term956 A B x''' y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5066873 A B x''' y f s)). Qed.
Lemma lem5066875 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5066876 {A B : Type'} (x''' : type1448 A B) (y : B) (s : A -> Prop) : (term957 A B x''' y s) = (term958 A B x''' y s).
Proof. exact (MK_COMB (@lem5066875 A B) (@lem5066874 A B x''' y s)). Qed.
Lemma lem5066877 {A B : Type'} (x''' : type1448 A B) (y : B) : (term959 A B x''' y) = (term960 A B x''' y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5066876 A B x''' y s)). Qed.
Lemma lem5066878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5066879 {A B : Type'} (x''' : type1448 A B) (y : B) : (term712 A B x''' y) = (term961 A B x''' y).
Proof. exact (MK_COMB (@lem5066878 A) (@lem5066877 A B x''' y)). Qed.
Lemma lem5066880 {A B : Type'} (x''' : type1448 A B) : (term714 A B x''') = (term962 A B x''').
Proof. exact (fun_ext (fun y : B => @lem5066879 A B x''' y)). Qed.
Lemma lem5066881 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5066882 {A B : Type'} (x''' : type1448 A B) : (term716 A B x''') = (term963 A B x''').
Proof. exact (MK_COMB (@lem5066881 B) (@lem5066880 A B x''')). Qed.
Lemma lem5066883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066891 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5066890 A (type686 A) f x). Qed.
Lemma lem5066892 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5066891 A (@IN A) x). Qed.
Lemma lem5066893 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066894 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5066892 A x) (@lem5066893 A s)). Qed.
Lemma lem5066896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066897 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5066896 (A -> Prop) Prop f x). Qed.
Lemma lem5066898 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term886 A x s).
Proof. exact (@lem5066897 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5066900 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term886 A x s).
Proof. exact (TRANS (@lem5066894 A x s) (@lem5066898 A x s)). Qed.
Lemma lem5066901 {A : Type'} (x : A) (s : A -> Prop) : (term887 A x s) = (term888 A x s).
Proof. exact (MK_COMB (@lem5066883) (@lem5066900 A x s)). Qed.
Lemma lem5066902 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5066909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066911 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5066909 A B f x). Qed.
Lemma lem5066912 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5066913 {A B : Type'} (y : B) (f : A -> B) (x : A) : (y = (f x)) = (y = (@I (A -> B) f x)).
Proof. exact (MK_COMB (@lem5066912 B y) (@lem5066911 A B f x)). Qed.
Lemma lem5066914 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term964 A B y f x) = (term965 A B y f x).
Proof. exact (MK_COMB (@lem5066902) (@lem5066913 A B y f x)). Qed.
Lemma lem5066915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066916 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term966 A B y f x) = (term967 A B y f x).
Proof. exact (MK_COMB (@lem5066915) (@lem5066914 A B y f x)). Qed.
Lemma lem5066917 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term544 A B y f x s) = (term968 A B y f x s).
Proof. exact (MK_COMB (@lem5066916 A B y f x) (@lem5066901 A x s)). Qed.
Lemma lem5066918 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term550 A B y f s) = (term969 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5066917 A B y f x s)). Qed.
Lemma lem5066919 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5066920 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term551 A B y f s) = (term970 A B y f s).
Proof. exact (MK_COMB (@lem5066919 A) (@lem5066918 A B y f s)). Qed.
Lemma lem5066929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066930 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5066929 (A -> B) (type678 A B) f x). Qed.
Lemma lem5066931 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5066930 A B (@IMAGE A B) f). Qed.
Lemma lem5066932 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5066933 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5066931 A B f) (@lem5066932 A s)). Qed.
Lemma lem5066935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066936 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5066935 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5066937 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term947 A B f s).
Proof. exact (@lem5066936 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5066939 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term947 A B f s).
Proof. exact (TRANS (@lem5066933 A B f s) (@lem5066937 A B f s)). Qed.
Lemma lem5066940 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem5066941 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term199 A B y f s) = (term948 A B y f s).
Proof. exact (MK_COMB (@lem5066940 B y) (@lem5066939 A B f s)). Qed.
Lemma lem5066943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066944 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5066943 B (type686 B) f x). Qed.
Lemma lem5066945 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem5066944 B (@IN B) y). Qed.
Lemma lem5066946 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term947 A B f s) = (term947 A B f s).
Proof. exact (eq_refl (term947 A B f s)). Qed.
Lemma lem5066947 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term949 A B y f s).
Proof. exact (MK_COMB (@lem5066945 B y) (@lem5066946 A B f s)). Qed.
Lemma lem5066949 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5066950 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5066949 (B -> Prop) Prop f x). Qed.
Lemma lem5066951 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term949 A B y f s) = (term950 A B y f s).
Proof. exact (@lem5066950 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term947 A B f s)). Qed.
Lemma lem5066952 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term950 A B y f s).
Proof. exact (TRANS (@lem5066947 A B y f s) (@lem5066951 A B y f s)). Qed.
Lemma lem5066953 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term199 A B y f s) = (term950 A B y f s).
Proof. exact (TRANS (@lem5066941 A B y f s) (@lem5066952 A B y f s)). Qed.
Lemma lem5066954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5066955 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term554 A B y f s) = (term971 A B y f s).
Proof. exact (MK_COMB (@lem5066954) (@lem5066953 A B y f s)). Qed.
Lemma lem5066956 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term556 A B y f s) = (term972 A B y f s).
Proof. exact (MK_COMB (@lem5066955 A B y f s) (@lem5066920 A B y f s)). Qed.
Lemma lem5066957 {A B : Type'} (y : B) (s : A -> Prop) : (term571 A B y s) = (term973 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5066956 A B y f s)). Qed.
Lemma lem5066958 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5066959 {A B : Type'} (y : B) (s : A -> Prop) : (term582 A B y s) = (term974 A B y s).
Proof. exact (MK_COMB (@lem5066958 A B) (@lem5066957 A B y s)). Qed.
Lemma lem5066960 {A B : Type'} (y : B) : (term593 A B y) = (term975 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5066959 A B y s)). Qed.
Lemma lem5066961 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5066962 {A B : Type'} (y : B) : (term604 A B y) = (term976 A B y).
Proof. exact (MK_COMB (@lem5066961 A) (@lem5066960 A B y)). Qed.
Lemma lem5066963 {A B : Type'} : (term615 A B) = (term977 A B).
Proof. exact (fun_ext (fun y : B => @lem5066962 A B y)). Qed.
Lemma lem5066964 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5066965 {A B : Type'} : (term626 A B) = (term978 A B).
Proof. exact (MK_COMB (@lem5066964 B) (@lem5066963 A B)). Qed.
Lemma lem5066966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5066967 {A B : Type'} : (term628 A B) = (term979 A B).
Proof. exact (MK_COMB (@lem5066966) (@lem5066965 A B)). Qed.
Lemma lem5066968 {A B : Type'} (x''' : type1448 A B) : (term731 A B x''') = (term980 A B x''').
Proof. exact (MK_COMB (@lem5066967 A B) (@lem5066882 A B x''')). Qed.
Lemma lem5066969 {A B : Type'} (x''' : type1448 A B) (h1 : term731 A B x''') : term980 A B x'''.
Proof. exact (EQ_MP (@lem5066968 A B x''') (@lem5066191 A B x''' h1)). Qed.
Lemma lem5067192 {A : Type'} (x''''' : A) (y : A) : (term981 A x''''' y) = (term981 A x''''' y).
Proof. exact (eq_refl (term981 A x''''' y)). Qed.
Lemma lem5067193 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5067198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5067198 A B f x). Qed.
Lemma lem5067201 {A B : Type'} (f : A -> B) (x''''' : A) : (f x''''') = (@I (A -> B) f x''''').
Proof. exact (@lem5067199 A B f x'''''). Qed.
Lemma lem5067206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067207 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5067206 A B f x). Qed.
Lemma lem5067209 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem5067207 A B f y). Qed.
Lemma lem5067210 {A B : Type'} (f : A -> B) (x''''' : A) : (term982 A B f x''''') = (term983 A B f x''''').
Proof. exact (MK_COMB (@lem5067193 B) (@lem5067201 A B f x''''')). Qed.
Lemma lem5067211 {A B : Type'} (x''''' : A) (f : A -> B) (y : A) : ((f x''''') = (f y)) = ((@I (A -> B) f x''''') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem5067210 A B f x''''') (@lem5067209 A B f y)). Qed.
Lemma lem5067218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067219 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5067218 A (type686 A) f x). Qed.
Lemma lem5067220 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem5067219 A (@IN A) y). Qed.
Lemma lem5067221 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067222 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem5067220 A y) (@lem5067221 A s)). Qed.
Lemma lem5067224 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067225 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5067224 (A -> Prop) Prop f x). Qed.
Lemma lem5067226 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term886 A y s).
Proof. exact (@lem5067225 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem5067228 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term886 A y s).
Proof. exact (TRANS (@lem5067222 A y s) (@lem5067226 A y s)). Qed.
Lemma lem5067229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067230 {A : Type'} (y : A) (s : A -> Prop) : (term984 A y s) = (term985 A y s).
Proof. exact (MK_COMB (@lem5067229) (@lem5067228 A y s)). Qed.
Lemma lem5067231 {A B : Type'} (s : A -> Prop) (x''''' : A) (f : A -> B) (y : A) : (term219 A B s x''''' f y) = (term986 A B s x''''' f y).
Proof. exact (MK_COMB (@lem5067230 A y s) (@lem5067211 A B x''''' f y)). Qed.
Lemma lem5067238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067239 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5067238 A (type686 A) f x). Qed.
Lemma lem5067240 {A : Type'} (x''''' : A) : (@IN A x''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''').
Proof. exact (@lem5067239 A (@IN A) x'''''). Qed.
Lemma lem5067241 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067242 {A : Type'} (x''''' : A) (s : A -> Prop) : (@IN A x''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''' s).
Proof. exact (MK_COMB (@lem5067240 A x''''') (@lem5067241 A s)). Qed.
Lemma lem5067244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067245 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5067244 (A -> Prop) Prop f x). Qed.
Lemma lem5067246 {A : Type'} (x''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''' s) = (term886 A x''''' s).
Proof. exact (@lem5067245 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''') s). Qed.
Lemma lem5067248 {A : Type'} (x''''' : A) (s : A -> Prop) : (@IN A x''''' s) = (term886 A x''''' s).
Proof. exact (TRANS (@lem5067242 A x''''' s) (@lem5067246 A x''''' s)). Qed.
Lemma lem5067249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067250 {A : Type'} (x''''' : A) (s : A -> Prop) : (term984 A x''''' s) = (term985 A x''''' s).
Proof. exact (MK_COMB (@lem5067249) (@lem5067248 A x''''' s)). Qed.
Lemma lem5067251 {A B : Type'} (s : A -> Prop) (x''''' : A) (f : A -> B) (y : A) : (term224 A B s x''''' f y) = (term987 A B s x''''' f y).
Proof. exact (MK_COMB (@lem5067250 A x''''' s) (@lem5067231 A B s x''''' f y)). Qed.
Lemma lem5067252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067253 {A B : Type'} (s : A -> Prop) (x''''' : A) (f : A -> B) (y : A) : (term988 A B s x''''' f y) = (term989 A B s x''''' f y).
Proof. exact (MK_COMB (@lem5067252) (@lem5067251 A B s x''''' f y)). Qed.
Lemma lem5067254 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) : (term243 A B s f x''''' y) = (term990 A B s f x''''' y).
Proof. exact (MK_COMB (@lem5067253 A B s x''''' f y) (@lem5067192 A x''''' y)). Qed.
Lemma lem5067255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5067256 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5067261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067262 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5067261 A B f x). Qed.
Lemma lem5067264 {A B : Type'} (f : A -> B) (x''''' : A) : (f x''''') = (@I (A -> B) f x''''').
Proof. exact (@lem5067262 A B f x'''''). Qed.
Lemma lem5067265 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5067266 {A B : Type'} (f : A -> B) (x''''' : A) : (term991 A B f x''''') = (term992 A B f x''''').
Proof. exact (MK_COMB (@lem5067256 B) (@lem5067264 A B f x''''')). Qed.
Lemma lem5067267 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term232 A B f x''''' t) = (term993 A B f x''''' t).
Proof. exact (MK_COMB (@lem5067266 A B f x''''') (@lem5067265 B t)). Qed.
Lemma lem5067269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067270 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5067269 B (type686 B) f x). Qed.
Lemma lem5067271 {A B : Type'} (f : A -> B) (x''''' : A) : (term992 A B f x''''') = (term994 A B f x''''').
Proof. exact (@lem5067270 B (@IN B) (@I (A -> B) f x''''')). Qed.
Lemma lem5067272 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5067273 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term993 A B f x''''' t) = (term995 A B f x''''' t).
Proof. exact (MK_COMB (@lem5067271 A B f x''''') (@lem5067272 B t)). Qed.
Lemma lem5067275 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067276 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5067275 (B -> Prop) Prop f x). Qed.
Lemma lem5067277 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term995 A B f x''''' t) = (term996 A B f x''''' t).
Proof. exact (@lem5067276 B (term994 A B f x''''') t). Qed.
Lemma lem5067278 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term993 A B f x''''' t) = (term996 A B f x''''' t).
Proof. exact (TRANS (@lem5067273 A B f x''''' t) (@lem5067277 A B f x''''' t)). Qed.
Lemma lem5067279 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term232 A B f x''''' t) = (term996 A B f x''''' t).
Proof. exact (TRANS (@lem5067267 A B f x''''' t) (@lem5067278 A B f x''''' t)). Qed.
Lemma lem5067280 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term997 A B f x''''' t) = (term998 A B f x''''' t).
Proof. exact (MK_COMB (@lem5067255) (@lem5067279 A B f x''''' t)). Qed.
Lemma lem5067287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067288 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5067287 A (type686 A) f x). Qed.
Lemma lem5067289 {A : Type'} (x''''' : A) : (@IN A x''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''').
Proof. exact (@lem5067288 A (@IN A) x'''''). Qed.
Lemma lem5067290 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067291 {A : Type'} (x''''' : A) (s : A -> Prop) : (@IN A x''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''' s).
Proof. exact (MK_COMB (@lem5067289 A x''''') (@lem5067290 A s)). Qed.
Lemma lem5067293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067294 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5067293 (A -> Prop) Prop f x). Qed.
Lemma lem5067295 {A : Type'} (x''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''' s) = (term886 A x''''' s).
Proof. exact (@lem5067294 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''') s). Qed.
Lemma lem5067297 {A : Type'} (x''''' : A) (s : A -> Prop) : (@IN A x''''' s) = (term886 A x''''' s).
Proof. exact (TRANS (@lem5067291 A x''''' s) (@lem5067295 A x''''' s)). Qed.
Lemma lem5067298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067299 {A : Type'} (x''''' : A) (s : A -> Prop) : (term984 A x''''' s) = (term985 A x''''' s).
Proof. exact (MK_COMB (@lem5067298) (@lem5067297 A x''''' s)). Qed.
Lemma lem5067300 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) : (term231 A B s f x''''' t) = (term999 A B s f x''''' t).
Proof. exact (MK_COMB (@lem5067299 A x''''' s) (@lem5067280 A B f x''''' t)). Qed.
Lemma lem5067301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5067302 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) : (term290 A B s f x''''' t) = (term1000 A B s f x''''' t).
Proof. exact (MK_COMB (@lem5067301) (@lem5067300 A B s f x''''' t)). Qed.
Lemma lem5067303 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) : (term306 A B t s f x''''' y) = (term1001 A B t s f x''''' y).
Proof. exact (MK_COMB (@lem5067302 A B s f x''''' t) (@lem5067254 A B s f x''''' y)). Qed.
Lemma lem5067308 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5067309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5067310 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5067315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067317 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5067315 A B f x). Qed.
Lemma lem5067322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5067322 A B f x). Qed.
Lemma lem5067325 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem5067323 A B f y). Qed.
Lemma lem5067326 {A B : Type'} (f : A -> B) (x : A) : (term982 A B f x) = (term983 A B f x).
Proof. exact (MK_COMB (@lem5067310 B) (@lem5067317 A B f x)). Qed.
Lemma lem5067327 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem5067326 A B f x) (@lem5067325 A B f y)). Qed.
Lemma lem5067328 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1002 A B x f y) = (term1003 A B x f y).
Proof. exact (MK_COMB (@lem5067309) (@lem5067327 A B x f y)). Qed.
Lemma lem5067329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5067336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067337 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5067336 A (type686 A) f x). Qed.
Lemma lem5067338 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem5067337 A (@IN A) y). Qed.
Lemma lem5067339 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067340 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem5067338 A y) (@lem5067339 A s)). Qed.
Lemma lem5067342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067343 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5067342 (A -> Prop) Prop f x). Qed.
Lemma lem5067344 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term886 A y s).
Proof. exact (@lem5067343 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem5067346 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term886 A y s).
Proof. exact (TRANS (@lem5067340 A y s) (@lem5067344 A y s)). Qed.
Lemma lem5067347 {A : Type'} (y : A) (s : A -> Prop) : (term887 A y s) = (term888 A y s).
Proof. exact (MK_COMB (@lem5067329) (@lem5067346 A y s)). Qed.
Lemma lem5067348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5067349 {A : Type'} (y : A) (s : A -> Prop) : (term215 A y s) = (term889 A y s).
Proof. exact (MK_COMB (@lem5067348) (@lem5067347 A y s)). Qed.
Lemma lem5067350 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term214 A B s x f y) = (term1004 A B s x f y).
Proof. exact (MK_COMB (@lem5067349 A y s) (@lem5067328 A B x f y)). Qed.
Lemma lem5067351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5067358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067359 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5067358 A (type686 A) f x). Qed.
Lemma lem5067360 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5067359 A (@IN A) x). Qed.
Lemma lem5067361 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067362 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5067360 A x) (@lem5067361 A s)). Qed.
Lemma lem5067364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067365 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5067364 (A -> Prop) Prop f x). Qed.
Lemma lem5067366 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term886 A x s).
Proof. exact (@lem5067365 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5067368 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term886 A x s).
Proof. exact (TRANS (@lem5067362 A x s) (@lem5067366 A x s)). Qed.
Lemma lem5067369 {A : Type'} (x : A) (s : A -> Prop) : (term887 A x s) = (term888 A x s).
Proof. exact (MK_COMB (@lem5067351) (@lem5067368 A x s)). Qed.
Lemma lem5067370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5067371 {A : Type'} (x : A) (s : A -> Prop) : (term215 A x s) = (term889 A x s).
Proof. exact (MK_COMB (@lem5067370) (@lem5067369 A x s)). Qed.
Lemma lem5067372 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term217 A B s x f y) = (term1005 A B s x f y).
Proof. exact (MK_COMB (@lem5067371 A x s) (@lem5067350 A B s x f y)). Qed.
Lemma lem5067373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5067374 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term221 A B s x f y) = (term1006 A B s x f y).
Proof. exact (MK_COMB (@lem5067373) (@lem5067372 A B s x f y)). Qed.
Lemma lem5067375 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term223 A B s f x y) = (term1007 A B s f x y).
Proof. exact (MK_COMB (@lem5067374 A B s x f y) (@lem5067308 A x y)). Qed.
Lemma lem5067376 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term225 A B s f x) = (term1008 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5067375 A B s f x y)). Qed.
Lemma lem5067377 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067378 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term226 A B s f x) = (term1009 A B s f x).
Proof. exact (MK_COMB (@lem5067377 A) (@lem5067376 A B s f x)). Qed.
Lemma lem5067379 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term227 A B s f) = (term1010 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5067378 A B s f x)). Qed.
Lemma lem5067380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067381 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term228 A B s f) = (term1011 A B s f).
Proof. exact (MK_COMB (@lem5067380 A) (@lem5067379 A B s f)). Qed.
Lemma lem5067382 {B : Type'} : (@SUBSET B) = (@SUBSET B).
Proof. exact (eq_refl (@SUBSET B)). Qed.
Lemma lem5067389 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067390 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5067389 (A -> B) (type678 A B) f x). Qed.
Lemma lem5067391 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5067390 A B (@IMAGE A B) f). Qed.
Lemma lem5067392 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5067393 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5067391 A B f) (@lem5067392 A s)). Qed.
Lemma lem5067395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067396 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5067395 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5067397 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term947 A B f s).
Proof. exact (@lem5067396 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5067399 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term947 A B f s).
Proof. exact (TRANS (@lem5067393 A B f s) (@lem5067397 A B f s)). Qed.
Lemma lem5067400 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5067401 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1012 A B f s) = (term1013 A B f s).
Proof. exact (MK_COMB (@lem5067382 B) (@lem5067399 A B f s)). Qed.
Lemma lem5067402 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term129 A B f s t) = (term1014 A B f s t).
Proof. exact (MK_COMB (@lem5067401 A B f s) (@lem5067400 B t)). Qed.
Lemma lem5067404 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067405 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5067404 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5067406 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1013 A B f s) = (term1015 A B f s).
Proof. exact (@lem5067405 B (@SUBSET B) (term947 A B f s)). Qed.
Lemma lem5067407 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5067408 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1014 A B f s t) = (term1016 A B f s t).
Proof. exact (MK_COMB (@lem5067406 A B f s) (@lem5067407 B t)). Qed.
Lemma lem5067410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5067411 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5067410 (B -> Prop) Prop f x). Qed.
Lemma lem5067412 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1016 A B f s t) = (term1017 A B f s t).
Proof. exact (@lem5067411 B (term1015 A B f s) t). Qed.
Lemma lem5067413 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1014 A B f s t) = (term1017 A B f s t).
Proof. exact (TRANS (@lem5067408 A B f s t) (@lem5067412 A B f s t)). Qed.
Lemma lem5067414 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term129 A B f s t) = (term1017 A B f s t).
Proof. exact (TRANS (@lem5067402 A B f s t) (@lem5067413 A B f s t)). Qed.
Lemma lem5067415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067416 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term212 A B f s t) = (term1018 A B f s t).
Proof. exact (MK_COMB (@lem5067415) (@lem5067414 A B f s t)). Qed.
Lemma lem5067417 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term229 A B t s f) = (term1019 A B t s f).
Proof. exact (MK_COMB (@lem5067416 A B f s t) (@lem5067381 A B s f)). Qed.
Lemma lem5067418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5067419 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term264 A B t s f) = (term1020 A B t s f).
Proof. exact (MK_COMB (@lem5067418) (@lem5067417 A B t s f)). Qed.
Lemma lem5067420 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) : (term335 A B t s f x''''' y) = (term1021 A B t s f x''''' y).
Proof. exact (MK_COMB (@lem5067419 A B t s f) (@lem5067303 A B t s f x''''' y)). Qed.
Lemma lem5067421 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1021 A B t s f x''''' y.
Proof. exact (EQ_MP (@lem5067420 A B t s f x''''' y) (@lem5066195 A B t s f x''''' y h1)). Qed.
Lemma lem5067422 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1001 A B t s f x''''' y.
Proof. exact (proj2 (@lem5067421 A B t s f x''''' y h1)). Qed.
Lemma lem5067423 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1019 A B t s f.
Proof. exact (proj1 (@lem5067421 A B t s f x''''' y h1)). Qed.
Lemma lem5067424 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1011 A B s f.
Proof. exact (proj2 (@lem5067423 A B t s f x''''' y h1)). Qed.
Lemma lem5067429 {A B : Type'} (x''' : type1448 A B) (h1 : term731 A B x''') : term978 A B.
Proof. exact (proj1 (@lem5066969 A B x''' h1)). Qed.
Lemma lem5067434 {B : Type'} (x : type638 B) (h1 : term882 B x) : term901 B.
Proof. exact (proj2 (@lem5066366 B x h1)). Qed.
Lemma lem5067436 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term999 A B s f x''''' t.
Proof. exact (h1). Qed.
Lemma lem5067437 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term990 A B s f x''''' y.
Proof. exact (h1). Qed.
Lemma lem5067441 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term987 A B s x''''' f y.
Proof. exact (proj1 (@lem5067437 A B s f x''''' y h1)). Qed.
Lemma lem5067442 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term986 A B s x''''' f y.
Proof. exact (proj2 (@lem5067441 A B s f x''''' y h1)). Qed.
Lemma lem5067564 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1022 A P Q) = (term1023 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5067565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1022 A P Q) = (term1023 A P Q).
Proof. exact (@lem5067564 A P Q). Qed.
Lemma lem5067566 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1024 A B y f s) = (term1025 A B y f s).
Proof. exact (@lem5067565 A (term950 A B y f s) (term969 A B y f s)). Qed.
Lemma lem5067567 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1026 A B y f s x) = (term968 A B y f x s).
Proof. exact (eq_refl (term1026 A B y f s x)). Qed.
Lemma lem5067568 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1027 A B y f s) = (term969 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5067567 A B y f x s)). Qed.
Lemma lem5067569 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067570 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1028 A B y f s) = (term970 A B y f s).
Proof. exact (MK_COMB (@lem5067569 A) (@lem5067568 A B y f s)). Qed.
Lemma lem5067571 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term971 A B y f s) = (term971 A B y f s).
Proof. exact (eq_refl (term971 A B y f s)). Qed.
Lemma lem5067572 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1024 A B y f s) = (term972 A B y f s).
Proof. exact (MK_COMB (@lem5067571 A B y f s) (@lem5067570 A B y f s)). Qed.
Lemma lem5067573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5067574 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1029 A B y f s) = (term1030 A B y f s).
Proof. exact (MK_COMB (@lem5067573) (@lem5067572 A B y f s)). Qed.
Lemma lem5067575 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1026 A B y f s x) = (term968 A B y f x s).
Proof. exact (eq_refl (term1026 A B y f s x)). Qed.
Lemma lem5067576 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term971 A B y f s) = (term971 A B y f s).
Proof. exact (eq_refl (term971 A B y f s)). Qed.
Lemma lem5067577 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1031 A B y f s x) = (term1032 A B y f x s).
Proof. exact (MK_COMB (@lem5067576 A B y f s) (@lem5067575 A B y f x s)). Qed.
Lemma lem5067578 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1033 A B y f s) = (term1034 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5067577 A B y f x s)). Qed.
Lemma lem5067579 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067580 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1025 A B y f s) = (term1035 A B y f s).
Proof. exact (MK_COMB (@lem5067579 A) (@lem5067578 A B y f s)). Qed.
Lemma lem5067581 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term1024 A B y f s) = (term1025 A B y f s)) = ((term972 A B y f s) = (term1035 A B y f s)).
Proof. exact (MK_COMB (@lem5067574 A B y f s) (@lem5067580 A B y f s)). Qed.
Lemma lem5067582 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term972 A B y f s) = (term1035 A B y f s).
Proof. exact (EQ_MP (@lem5067581 A B y f s) (@lem5067566 A B y f s)). Qed.
Lemma lem5067583 {A B : Type'} (y : B) (s : A -> Prop) : (term973 A B y s) = (term1036 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5067582 A B y f s)). Qed.
Lemma lem5067584 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5067585 {A B : Type'} (y : B) (s : A -> Prop) : (term974 A B y s) = (term1037 A B y s).
Proof. exact (MK_COMB (@lem5067584 A B) (@lem5067583 A B y s)). Qed.
Lemma lem5067586 {A B : Type'} (y : B) : (term975 A B y) = (term1038 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5067585 A B y s)). Qed.
Lemma lem5067587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5067588 {A B : Type'} (y : B) : (term976 A B y) = (term1039 A B y).
Proof. exact (MK_COMB (@lem5067587 A) (@lem5067586 A B y)). Qed.
Lemma lem5067589 {A B : Type'} : (term977 A B) = (term1040 A B).
Proof. exact (fun_ext (fun y : B => @lem5067588 A B y)). Qed.
Lemma lem5067590 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5067591 {A B : Type'} : (term978 A B) = (term1041 A B).
Proof. exact (MK_COMB (@lem5067590 B) (@lem5067589 A B)). Qed.
Lemma lem5067604 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1032 A B y f x s) = (term1032 A B y f x s).
Proof. exact (eq_refl (term1032 A B y f x s)). Qed.
Lemma lem5067605 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1034 A B y f s) = (term1034 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5067604 A B y f x s)). Qed.
Lemma lem5067606 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067607 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1035 A B y f s) = (term1035 A B y f s).
Proof. exact (MK_COMB (@lem5067606 A) (@lem5067605 A B y f s)). Qed.
Lemma lem5067608 {A B : Type'} (y : B) (s : A -> Prop) : (term1036 A B y s) = (term1036 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5067607 A B y f s)). Qed.
Lemma lem5067609 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5067610 {A B : Type'} (y : B) (s : A -> Prop) : (term1037 A B y s) = (term1037 A B y s).
Proof. exact (MK_COMB (@lem5067609 A B) (@lem5067608 A B y s)). Qed.
Lemma lem5067611 {A B : Type'} (y : B) : (term1038 A B y) = (term1038 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5067610 A B y s)). Qed.
Lemma lem5067612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5067613 {A B : Type'} (y : B) : (term1039 A B y) = (term1039 A B y).
Proof. exact (MK_COMB (@lem5067612 A) (@lem5067611 A B y)). Qed.
Lemma lem5067614 {A B : Type'} : (term1040 A B) = (term1040 A B).
Proof. exact (fun_ext (fun y : B => @lem5067613 A B y)). Qed.
Lemma lem5067615 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5067616 {A B : Type'} : (term1041 A B) = (term1041 A B).
Proof. exact (MK_COMB (@lem5067615 B) (@lem5067614 A B)). Qed.
Lemma lem5067617 {A B : Type'} : (term978 A B) = (term1041 A B).
Proof. exact (TRANS (@lem5067591 A B) (@lem5067616 A B)). Qed.
Lemma lem5067618 {A B : Type'} (x''' : type1448 A B) (h1 : term731 A B x''') : term1041 A B.
Proof. exact (EQ_MP (@lem5067617 A B) (@lem5067429 A B x''' h1)). Qed.
Lemma lem5067836 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1022 A P Q) = (term1023 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5067837 {B : Type'} (P : Prop) (Q : B -> Prop) : (term1022 B P Q) = (term1023 B P Q).
Proof. exact (@lem5067836 B P Q). Qed.
Lemma lem5067838 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1042 B s t) = (term1043 B s t).
Proof. exact (@lem5067837 B (term895 B s t) (term891 B s t)). Qed.
Lemma lem5067839 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1044 B s t x) = (term890 B s x t).
Proof. exact (eq_refl (term1044 B s t x)). Qed.
Lemma lem5067840 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1045 B s t) = (term891 B s t).
Proof. exact (fun_ext (fun x : B => @lem5067839 B s x t)). Qed.
Lemma lem5067841 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5067842 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1046 B s t) = (term892 B s t).
Proof. exact (MK_COMB (@lem5067841 B) (@lem5067840 B s t)). Qed.
Lemma lem5067843 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term896 B s t) = (term896 B s t).
Proof. exact (eq_refl (term896 B s t)). Qed.
Lemma lem5067844 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1042 B s t) = (term897 B s t).
Proof. exact (MK_COMB (@lem5067843 B s t) (@lem5067842 B s t)). Qed.
Lemma lem5067845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5067846 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1047 B s t) = (term1048 B s t).
Proof. exact (MK_COMB (@lem5067845) (@lem5067844 B s t)). Qed.
Lemma lem5067847 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1044 B s t x) = (term890 B s x t).
Proof. exact (eq_refl (term1044 B s t x)). Qed.
Lemma lem5067848 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term896 B s t) = (term896 B s t).
Proof. exact (eq_refl (term896 B s t)). Qed.
Lemma lem5067849 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1049 B s t x) = (term1050 B s x t).
Proof. exact (MK_COMB (@lem5067848 B s t) (@lem5067847 B s x t)). Qed.
Lemma lem5067850 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1051 B s t) = (term1052 B s t).
Proof. exact (fun_ext (fun x : B => @lem5067849 B s x t)). Qed.
Lemma lem5067851 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5067852 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1043 B s t) = (term1053 B s t).
Proof. exact (MK_COMB (@lem5067851 B) (@lem5067850 B s t)). Qed.
Lemma lem5067853 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1042 B s t) = (term1043 B s t)) = ((term897 B s t) = (term1053 B s t)).
Proof. exact (MK_COMB (@lem5067846 B s t) (@lem5067852 B s t)). Qed.
Lemma lem5067854 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term897 B s t) = (term1053 B s t).
Proof. exact (EQ_MP (@lem5067853 B s t) (@lem5067838 B s t)). Qed.
Lemma lem5067855 {B : Type'} (s : B -> Prop) : (term898 B s) = (term1054 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5067854 B s t)). Qed.
Lemma lem5067856 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5067857 {B : Type'} (s : B -> Prop) : (term899 B s) = (term1055 B s).
Proof. exact (MK_COMB (@lem5067856 B) (@lem5067855 B s)). Qed.
Lemma lem5067858 {B : Type'} : (term900 B) = (term1056 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5067857 B s)). Qed.
Lemma lem5067859 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5067860 {B : Type'} : (term901 B) = (term1057 B).
Proof. exact (MK_COMB (@lem5067859 B) (@lem5067858 B)). Qed.
Lemma lem5067873 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1050 B s x t) = (term1050 B s x t).
Proof. exact (eq_refl (term1050 B s x t)). Qed.
Lemma lem5067874 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1052 B s t) = (term1052 B s t).
Proof. exact (fun_ext (fun x : B => @lem5067873 B s x t)). Qed.
Lemma lem5067875 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5067876 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1053 B s t) = (term1053 B s t).
Proof. exact (MK_COMB (@lem5067875 B) (@lem5067874 B s t)). Qed.
Lemma lem5067877 {B : Type'} (s : B -> Prop) : (term1054 B s) = (term1054 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5067876 B s t)). Qed.
Lemma lem5067878 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5067879 {B : Type'} (s : B -> Prop) : (term1055 B s) = (term1055 B s).
Proof. exact (MK_COMB (@lem5067878 B) (@lem5067877 B s)). Qed.
Lemma lem5067880 {B : Type'} : (term1056 B) = (term1056 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5067879 B s)). Qed.
Lemma lem5067881 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5067882 {B : Type'} : (term1057 B) = (term1057 B).
Proof. exact (MK_COMB (@lem5067881 B) (@lem5067880 B)). Qed.
Lemma lem5067883 {B : Type'} : (term901 B) = (term1057 B).
Proof. exact (TRANS (@lem5067860 B) (@lem5067882 B)). Qed.
Lemma lem5067884 {B : Type'} (x : type638 B) (h1 : term882 B x) : term1057 B.
Proof. exact (EQ_MP (@lem5067883 B) (@lem5067434 B x h1)). Qed.
Lemma lem5067916 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1007 A B s f x y) = (term1007 A B s f x y).
Proof. exact (eq_refl (term1007 A B s f x y)). Qed.
Lemma lem5067917 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1008 A B s f x) = (term1008 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5067916 A B s f x y)). Qed.
Lemma lem5067918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067919 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1009 A B s f x) = (term1009 A B s f x).
Proof. exact (MK_COMB (@lem5067918 A) (@lem5067917 A B s f x)). Qed.
Lemma lem5067920 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1010 A B s f) = (term1010 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5067919 A B s f x)). Qed.
Lemma lem5067921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5067923 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1011 A B s f) = (term1011 A B s f).
Proof. exact (MK_COMB (@lem5067921 A) (@lem5067920 A B s f)). Qed.
Lemma lem5067924 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1011 A B s f.
Proof. exact (EQ_MP (@lem5067923 A B s f) (@lem5067424 A B t s f x''''' y h1)). Qed.
Lemma lem5068375 {A B : Type'} (_65009 : B) (x''' : type1448 A B) (h1 : term731 A B x''') : term1058 A B _65009.
Proof. exact (@lem5067618 A B x''' h1 _65009). Qed.
Lemma lem5068376 {A B : Type'} (_65009 : B) : (term1058 A B _65009) = (term1039 A B _65009).
Proof. exact (eq_refl (term1058 A B _65009)). Qed.
Lemma lem5068377 {A B : Type'} (_65009 : B) (x''' : type1448 A B) (h1 : term731 A B x''') : term1039 A B _65009.
Proof. exact (EQ_MP (@lem5068376 A B _65009) (@lem5068375 A B _65009 x''' h1)). Qed.
Lemma lem5068378 {A B : Type'} (_65009 : B) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1059 A B _65009 _65010.
Proof. exact (@lem5068377 A B _65009 x''' h1 _65010). Qed.
Lemma lem5068379 {A B : Type'} (_65009 : B) (_65010 : A -> Prop) : (term1059 A B _65009 _65010) = (term1037 A B _65009 _65010).
Proof. exact (eq_refl (term1059 A B _65009 _65010)). Qed.
Lemma lem5068380 {A B : Type'} (_65009 : B) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1037 A B _65009 _65010.
Proof. exact (EQ_MP (@lem5068379 A B _65009 _65010) (@lem5068378 A B _65009 _65010 x''' h1)). Qed.
Lemma lem5068381 {A B : Type'} (_65009 : B) (_65010 : A -> Prop) (_65011 : A -> B) (x''' : type1448 A B) (h1 : term731 A B x''') : term1060 A B _65009 _65010 _65011.
Proof. exact (@lem5068380 A B _65009 _65010 x''' h1 _65011). Qed.
Lemma lem5068382 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) : (term1060 A B _65009 _65010 _65011) = (term1035 A B _65009 _65011 _65010).
Proof. exact (eq_refl (term1060 A B _65009 _65010 _65011)). Qed.
Lemma lem5068383 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1035 A B _65009 _65011 _65010.
Proof. exact (EQ_MP (@lem5068382 A B _65009 _65011 _65010) (@lem5068381 A B _65009 _65010 _65011 x''' h1)). Qed.
Lemma lem5068384 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) (_65012 : A) (x''' : type1448 A B) (h1 : term731 A B x''') : term1061 A B _65009 _65011 _65010 _65012.
Proof. exact (@lem5068383 A B _65009 _65011 _65010 x''' h1 _65012). Qed.
Lemma lem5068385 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) : (term1061 A B _65009 _65011 _65010 _65012) = (term1032 A B _65009 _65011 _65012 _65010).
Proof. exact (eq_refl (term1061 A B _65009 _65011 _65010 _65012)). Qed.
Lemma lem5068438 {B : Type'} (_65030 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1062 B _65030.
Proof. exact (@lem5067884 B x h1 _65030). Qed.
Lemma lem5068439 {B : Type'} (_65030 : B -> Prop) : (term1062 B _65030) = (term1055 B _65030).
Proof. exact (eq_refl (term1062 B _65030)). Qed.
Lemma lem5068440 {B : Type'} (_65030 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1055 B _65030.
Proof. exact (EQ_MP (@lem5068439 B _65030) (@lem5068438 B _65030 x h1)). Qed.
Lemma lem5068441 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1063 B _65030 _65031.
Proof. exact (@lem5068440 B _65030 x h1 _65031). Qed.
Lemma lem5068442 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1063 B _65030 _65031) = (term1053 B _65030 _65031).
Proof. exact (eq_refl (term1063 B _65030 _65031)). Qed.
Lemma lem5068443 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1053 B _65030 _65031.
Proof. exact (EQ_MP (@lem5068442 B _65030 _65031) (@lem5068441 B _65030 _65031 x h1)). Qed.
Lemma lem5068444 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) (_65032 : B) (x : type638 B) (h1 : term882 B x) : term1064 B _65030 _65031 _65032.
Proof. exact (@lem5068443 B _65030 _65031 x h1 _65032). Qed.
Lemma lem5068445 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) : (term1064 B _65030 _65031 _65032) = (term1050 B _65030 _65032 _65031).
Proof. exact (eq_refl (term1064 B _65030 _65031 _65032)). Qed.
Lemma lem5068447 {A B : Type'} (_65033 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1065 A B s f _65033.
Proof. exact (@lem5067924 A B t s f x''''' y h1 _65033). Qed.
Lemma lem5068448 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) : (term1065 A B s f _65033) = (term1009 A B s f _65033).
Proof. exact (eq_refl (term1065 A B s f _65033)). Qed.
Lemma lem5068449 {A B : Type'} (_65033 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1009 A B s f _65033.
Proof. exact (EQ_MP (@lem5068448 A B s f _65033) (@lem5068447 A B _65033 t s f x''''' y h1)). Qed.
Lemma lem5068450 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1066 A B s f _65033 _65034.
Proof. exact (@lem5068449 A B _65033 t s f x''''' y h1 _65034). Qed.
Lemma lem5068451 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1066 A B s f _65033 _65034) = (term1007 A B s f _65033 _65034).
Proof. exact (eq_refl (term1066 A B s f _65033 _65034)). Qed.
Lemma lem5068452 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1007 A B s f _65033 _65034.
Proof. exact (EQ_MP (@lem5068451 A B s f _65033 _65034) (@lem5068450 A B _65033 _65034 t s f x''''' y h1)). Qed.
Lemma lem5068605 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1032 A B _65009 _65011 _65012 _65010.
Proof. exact (EQ_MP (@lem5068385 A B _65009 _65011 _65012 _65010) (@lem5068384 A B _65009 _65011 _65010 _65012 x''' h1)). Qed.
Lemma lem5068635 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1050 B _65030 _65032 _65031.
Proof. exact (EQ_MP (@lem5068445 B _65030 _65032 _65031) (@lem5068444 B _65030 _65031 _65032 x h1)). Qed.
Lemma lem5068639 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term998 A B f x''''' t.
Proof. exact (proj2 (@lem5067436 A B s f x''''' t h1)). Qed.
Lemma lem5068705 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1007 A B s f _65033 _65034) = (term1067 A B s f _65033 _65034).
Proof. exact (@lem5056442 (term888 A _65033 s) (term1004 A B s _65033 f _65034) (_65033 = _65034)). Qed.
Lemma lem5068712 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1068 A B s f _65033 _65034) = (term1069 A B s f _65033 _65034).
Proof. exact (@lem5056442 (term888 A _65034 s) (term1003 A B _65033 f _65034) (_65033 = _65034)). Qed.
Lemma lem5068713 {A : Type'} (_65033 : A) (s : A -> Prop) : (term889 A _65033 s) = (term889 A _65033 s).
Proof. exact (eq_refl (term889 A _65033 s)). Qed.
Lemma lem5068716 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1067 A B s f _65033 _65034) = (term1070 A B s f _65033 _65034).
Proof. exact (MK_COMB (@lem5068713 A _65033 s) (@lem5068712 A B s f _65033 _65034)). Qed.
Lemma lem5068718 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1007 A B s f _65033 _65034) = (term1070 A B s f _65033 _65034).
Proof. exact (TRANS (@lem5068705 A B s f _65033 _65034) (@lem5068716 A B s f _65033 _65034)). Qed.
Lemma lem5068719 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1070 A B s f _65033 _65034.
Proof. exact (EQ_MP (@lem5068718 A B s f _65033 _65034) (@lem5068452 A B _65033 _65034 t s f x''''' y h1)). Qed.
Lemma lem5068771 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term981 A x''''' y.
Proof. exact (proj2 (@lem5067437 A B s f x''''' y h1)). Qed.
Lemma lem5069331 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1017 A B f s t.
Proof. exact (proj1 (@lem5067423 A B t s f x''''' y h1)). Qed.
Lemma lem5069332 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1071 A B f s t.
Proof. exact (fun h0 : term1072 A B f s t => @lem5069331 A B t s f x''''' y h1). Qed.
Lemma lem5069334 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069335 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1071 A B f s t) = (term1017 A B f s t).
Proof. exact (@lem5069334 (term1017 A B f s t)). Qed.
Lemma lem5069336 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1017 A B f s t.
Proof. exact (EQ_MP (@lem5069335 A B f s t) (@lem5069332 A B t s f x''''' y h1)). Qed.
Lemma lem5069338 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5069339 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5069338 B x). Qed.
Lemma lem5069340 {A B : Type'} (f : A -> B) (x''''' : A) : (@I (A -> B) f x''''') = (@I (A -> B) f x''''').
Proof. exact (@lem5069339 B (@I (A -> B) f x''''')). Qed.
Lemma lem5069341 {A B : Type'} (f : A -> B) (x''''' : A) : term1074 A B f x'''''.
Proof. exact (fun h0 : term1075 A B f x''''' => @lem5069340 A B f x'''''). Qed.
Lemma lem5069343 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069344 {A B : Type'} (f : A -> B) (x''''' : A) : (term1074 A B f x''''') = ((@I (A -> B) f x''''') = (@I (A -> B) f x''''')).
Proof. exact (@lem5069343 ((@I (A -> B) f x''''') = (@I (A -> B) f x'''''))). Qed.
Lemma lem5069345 {A B : Type'} (f : A -> B) (x''''' : A) : (@I (A -> B) f x''''') = (@I (A -> B) f x''''').
Proof. exact (EQ_MP (@lem5069344 A B f x''''') (@lem5069341 A B f x''''')). Qed.
Lemma lem5069347 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term886 A x''''' s.
Proof. exact (proj1 (@lem5067436 A B s f x''''' t h1)). Qed.
Lemma lem5069348 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term1076 A x''''' s.
Proof. exact (fun h0 : term888 A x''''' s => @lem5069347 A B s f x''''' t h1). Qed.
Lemma lem5069350 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069351 {A : Type'} (x''''' : A) (s : A -> Prop) : (term1076 A x''''' s) = (term886 A x''''' s).
Proof. exact (@lem5069350 (term886 A x''''' s)). Qed.
Lemma lem5069352 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term886 A x''''' s.
Proof. exact (EQ_MP (@lem5069351 A x''''' s) (@lem5069348 A B s f x''''' t h1)). Qed.
Lemma lem5069354 (b : Prop) (a : Prop) : (a \/ b) = (term1077 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5069355 {A B : Type'} (_65012 : A) (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) : (term1032 A B _65009 _65011 _65012 _65010) = (term1078 A B _65012 _65009 _65011 _65010).
Proof. exact (@lem5069354 (term968 A B _65009 _65011 _65012 _65010) (term950 A B _65009 _65011 _65010)). Qed.
Lemma lem5069357 (a : Prop) (b : Prop) : (term1079 a b) = (term1080 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5069358 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) : (term1081 A B _65009 _65011 _65012 _65010) = (term1082 A B _65009 _65011 _65012 _65010).
Proof. exact (@lem5069357 (term965 A B _65009 _65011 _65012) (term888 A _65012 _65010)). Qed.
Lemma lem5069360 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5069361 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) : (term1084 A B _65009 _65011 _65012) = (_65009 = (@I (A -> B) _65011 _65012)).
Proof. exact (@lem5069360 (_65009 = (@I (A -> B) _65011 _65012))). Qed.
Lemma lem5069362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5069363 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) : (term1085 A B _65009 _65011 _65012) = (term1086 A B _65009 _65011 _65012).
Proof. exact (MK_COMB (@lem5069362) (@lem5069361 A B _65009 _65011 _65012)). Qed.
Lemma lem5069365 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5069366 {A : Type'} (_65012 : A) (_65010 : A -> Prop) : (term1087 A _65012 _65010) = (term886 A _65012 _65010).
Proof. exact (@lem5069365 (term886 A _65012 _65010)). Qed.
Lemma lem5069367 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) : (term1082 A B _65009 _65011 _65012 _65010) = (term1088 A B _65009 _65011 _65012 _65010).
Proof. exact (MK_COMB (@lem5069363 A B _65009 _65011 _65012) (@lem5069366 A _65012 _65010)). Qed.
Lemma lem5069368 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) : (term1081 A B _65009 _65011 _65012 _65010) = (term1088 A B _65009 _65011 _65012 _65010).
Proof. exact (TRANS (@lem5069358 A B _65009 _65011 _65012 _65010) (@lem5069367 A B _65009 _65011 _65012 _65010)). Qed.
Lemma lem5069369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5069370 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65012 : A) (_65010 : A -> Prop) : (term1089 A B _65009 _65011 _65012 _65010) = (term1090 A B _65009 _65011 _65012 _65010).
Proof. exact (MK_COMB (@lem5069369) (@lem5069368 A B _65009 _65011 _65012 _65010)). Qed.
Lemma lem5069371 {A B : Type'} (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) : (term950 A B _65009 _65011 _65010) = (term950 A B _65009 _65011 _65010).
Proof. exact (eq_refl (term950 A B _65009 _65011 _65010)). Qed.
Lemma lem5069372 {A B : Type'} (_65012 : A) (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) : (term1078 A B _65012 _65009 _65011 _65010) = (term1091 A B _65012 _65009 _65011 _65010).
Proof. exact (MK_COMB (@lem5069370 A B _65009 _65011 _65012 _65010) (@lem5069371 A B _65009 _65011 _65010)). Qed.
Lemma lem5069373 {A B : Type'} (_65012 : A) (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) : (term1032 A B _65009 _65011 _65012 _65010) = (term1091 A B _65012 _65009 _65011 _65010).
Proof. exact (TRANS (@lem5069355 A B _65012 _65009 _65011 _65010) (@lem5069372 A B _65012 _65009 _65011 _65010)). Qed.
Lemma lem5069375 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term1092 A B f x''''' s.
Proof. exact (conj (@lem5069345 A B f x''''') (@lem5069352 A B s f x''''' t h1)). Qed.
Lemma lem5069377 {A B : Type'} (_65012 : A) (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1091 A B _65012 _65009 _65011 _65010.
Proof. exact (EQ_MP (@lem5069373 A B _65012 _65009 _65011 _65010) (@lem5068605 A B _65009 _65011 _65012 _65010 x''' h1)). Qed.
Lemma lem5069378 {A B : Type'} (_65012 : A) (_65009 : B) (_65011 : A -> B) (_65010 : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1091 A B _65012 _65009 _65011 _65010.
Proof. exact (@lem5069377 A B _65012 _65009 _65011 _65010 x''' h1). Qed.
Lemma lem5069379 {A B : Type'} (x''''' : A) (f : A -> B) (s : A -> Prop) (x''' : type1448 A B) (h1 : term731 A B x''') : term1093 A B x''''' f s.
Proof. exact (@lem5069378 A B x''''' (@I (A -> B) f x''''') f s x''' h1). Qed.
Lemma lem5069382 {A B : Type'} (x''' : type1448 A B) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term999 A B s f x''''' t) : term1094 A B x''''' f s.
Proof. exact (@lem5069379 A B x''''' f s x''' h1 (@lem5069375 A B s f x''''' t h2)). Qed.
Lemma lem5069383 {A B : Type'} (x''' : type1448 A B) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term999 A B s f x''''' t) : term1095 A B x''''' f s.
Proof. exact (fun h0 : term1096 A B x''''' f s => @lem5069382 A B x''' s f x''''' t h1 h2). Qed.
Lemma lem5069385 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069386 {A B : Type'} (x''''' : A) (f : A -> B) (s : A -> Prop) : (term1095 A B x''''' f s) = (term1094 A B x''''' f s).
Proof. exact (@lem5069385 (term1094 A B x''''' f s)). Qed.
Lemma lem5069387 {A B : Type'} (x''' : type1448 A B) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term999 A B s f x''''' t) : term1094 A B x''''' f s.
Proof. exact (EQ_MP (@lem5069386 A B x''''' f s) (@lem5069383 A B x''' s f x''''' t h1 h2)). Qed.
Lemma lem5069393 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5069394 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) : (term1050 B _65030 _65032 _65031) = (term1097 B _65030 _65032 _65031).
Proof. exact (@lem5069393 (term888 B _65032 _65030) (term895 B _65030 _65031) (term886 B _65032 _65031)). Qed.
Lemma lem5069408 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5069409 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1098 B _65030 _65032 _65031) = (term1099 B _65032 _65030 _65031).
Proof. exact (@lem5069408 (term886 B _65032 _65031) (term895 B _65030 _65031)). Qed.
Lemma lem5069415 {B : Type'} (_65032 : B) (_65030 : B -> Prop) : (term889 B _65032 _65030) = (term889 B _65032 _65030).
Proof. exact (eq_refl (term889 B _65032 _65030)). Qed.
Lemma lem5069416 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1097 B _65030 _65032 _65031) = (term1100 B _65032 _65030 _65031).
Proof. exact (MK_COMB (@lem5069415 B _65032 _65030) (@lem5069409 B _65032 _65030 _65031)). Qed.
Lemma lem5069420 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5069421 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1100 B _65032 _65030 _65031) = (term1101 B _65032 _65030 _65031).
Proof. exact (@lem5069420 (term886 B _65032 _65031) (term888 B _65032 _65030) (term895 B _65030 _65031)). Qed.
Lemma lem5069437 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1097 B _65030 _65032 _65031) = (term1101 B _65032 _65030 _65031).
Proof. exact (TRANS (@lem5069416 B _65032 _65030 _65031) (@lem5069421 B _65032 _65030 _65031)). Qed.
Lemma lem5069438 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1050 B _65030 _65032 _65031) = (term1101 B _65032 _65030 _65031).
Proof. exact (TRANS (@lem5069394 B _65030 _65032 _65031) (@lem5069437 B _65032 _65030 _65031)). Qed.
Lemma lem5069439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5069440 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1102 B _65030 _65032 _65031) = (term1103 B _65032 _65030 _65031).
Proof. exact (MK_COMB (@lem5069439) (@lem5069438 B _65032 _65030 _65031)). Qed.
Lemma lem5069454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5069455 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1104 B _65031 _65032 _65030) = (term1105 B _65032 _65030 _65031).
Proof. exact (@lem5069454 (term888 B _65032 _65030) (term895 B _65030 _65031)). Qed.
Lemma lem5069461 {B : Type'} (_65032 : B) (_65031 : B -> Prop) : (term1106 B _65032 _65031) = (term1106 B _65032 _65031).
Proof. exact (eq_refl (term1106 B _65032 _65031)). Qed.
Lemma lem5069462 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1107 B _65031 _65032 _65030) = (term1101 B _65032 _65030 _65031).
Proof. exact (MK_COMB (@lem5069461 B _65032 _65031) (@lem5069455 B _65032 _65030 _65031)). Qed.
Lemma lem5069473 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : ((term1050 B _65030 _65032 _65031) = (term1107 B _65031 _65032 _65030)) = ((term1101 B _65032 _65030 _65031) = (term1101 B _65032 _65030 _65031)).
Proof. exact (MK_COMB (@lem5069440 B _65032 _65030 _65031) (@lem5069462 B _65032 _65030 _65031)). Qed.
Lemma lem5069475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5069476 (x : Prop) : (x = x) = True.
Proof. exact (@lem5069475 Prop x). Qed.
Lemma lem5069477 {B : Type'} (_65032 : B) (_65030 : B -> Prop) (_65031 : B -> Prop) : ((term1101 B _65032 _65030 _65031) = (term1101 B _65032 _65030 _65031)) = True.
Proof. exact (@lem5069476 (term1101 B _65032 _65030 _65031)). Qed.
Lemma lem5069478 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : ((term1050 B _65030 _65032 _65031) = (term1107 B _65031 _65032 _65030)) = True.
Proof. exact (TRANS (@lem5069473 B _65032 _65030 _65031) (@lem5069477 B _65032 _65030 _65031)). Qed.
Lemma lem5069479 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : True = ((term1050 B _65030 _65032 _65031) = (term1107 B _65031 _65032 _65030)).
Proof. exact (SYM (@lem5069478 B _65031 _65032 _65030)). Qed.
Lemma lem5069480 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : (term1050 B _65030 _65032 _65031) = (term1107 B _65031 _65032 _65030).
Proof. exact (EQ_MP (@lem5069479 B _65031 _65032 _65030) (@lem0)). Qed.
Lemma lem5069481 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1107 B _65031 _65032 _65030.
Proof. exact (EQ_MP (@lem5069480 B _65031 _65032 _65030) (@lem5068635 B _65030 _65032 _65031 x h1)). Qed.
Lemma lem5069483 (b : Prop) (a : Prop) : (a \/ b) = (term1077 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5069484 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) : (term1107 B _65031 _65032 _65030) = (term1108 B _65030 _65032 _65031).
Proof. exact (@lem5069483 (term1104 B _65031 _65032 _65030) (term886 B _65032 _65031)). Qed.
Lemma lem5069486 (a : Prop) (b : Prop) : (term1079 a b) = (term1080 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5069487 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : (term1109 B _65031 _65032 _65030) = (term1110 B _65031 _65032 _65030).
Proof. exact (@lem5069486 (term895 B _65030 _65031) (term888 B _65032 _65030)). Qed.
Lemma lem5069489 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5069490 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1111 B _65030 _65031) = (term893 B _65030 _65031).
Proof. exact (@lem5069489 (term893 B _65030 _65031)). Qed.
Lemma lem5069491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5069492 {B : Type'} (_65030 : B -> Prop) (_65031 : B -> Prop) : (term1112 B _65030 _65031) = (term1113 B _65030 _65031).
Proof. exact (MK_COMB (@lem5069491) (@lem5069490 B _65030 _65031)). Qed.
Lemma lem5069494 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5069495 {B : Type'} (_65032 : B) (_65030 : B -> Prop) : (term1087 B _65032 _65030) = (term886 B _65032 _65030).
Proof. exact (@lem5069494 (term886 B _65032 _65030)). Qed.
Lemma lem5069496 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : (term1110 B _65031 _65032 _65030) = (term1114 B _65031 _65032 _65030).
Proof. exact (MK_COMB (@lem5069492 B _65030 _65031) (@lem5069495 B _65032 _65030)). Qed.
Lemma lem5069497 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : (term1109 B _65031 _65032 _65030) = (term1114 B _65031 _65032 _65030).
Proof. exact (TRANS (@lem5069487 B _65031 _65032 _65030) (@lem5069496 B _65031 _65032 _65030)). Qed.
Lemma lem5069498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5069499 {B : Type'} (_65031 : B -> Prop) (_65032 : B) (_65030 : B -> Prop) : (term1115 B _65031 _65032 _65030) = (term1116 B _65031 _65032 _65030).
Proof. exact (MK_COMB (@lem5069498) (@lem5069497 B _65031 _65032 _65030)). Qed.
Lemma lem5069500 {B : Type'} (_65032 : B) (_65031 : B -> Prop) : (term886 B _65032 _65031) = (term886 B _65032 _65031).
Proof. exact (eq_refl (term886 B _65032 _65031)). Qed.
Lemma lem5069501 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) : (term1108 B _65030 _65032 _65031) = (term1117 B _65030 _65032 _65031).
Proof. exact (MK_COMB (@lem5069499 B _65031 _65032 _65030) (@lem5069500 B _65032 _65031)). Qed.
Lemma lem5069502 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) : (term1107 B _65031 _65032 _65030) = (term1117 B _65030 _65032 _65031).
Proof. exact (TRANS (@lem5069484 B _65030 _65032 _65031) (@lem5069501 B _65030 _65032 _65031)). Qed.
Lemma lem5069504 {A B : Type'} (x''' : type1448 A B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term335 A B t s f x''''' y) (h3 : term999 A B s f x''''' t) : term1118 A B t x''''' f s.
Proof. exact (conj (@lem5069336 A B t s f x''''' y h2) (@lem5069387 A B x''' s f x''''' t h1 h3)). Qed.
Lemma lem5069506 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1117 B _65030 _65032 _65031.
Proof. exact (EQ_MP (@lem5069502 B _65030 _65032 _65031) (@lem5069481 B _65031 _65032 _65030 x h1)). Qed.
Lemma lem5069507 {B : Type'} (_65030 : B -> Prop) (_65032 : B) (_65031 : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1117 B _65030 _65032 _65031.
Proof. exact (@lem5069506 B _65030 _65032 _65031 x h1). Qed.
Lemma lem5069508 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (x : type638 B) (h1 : term882 B x) : term1119 A B s f x''''' t.
Proof. exact (@lem5069507 B (term947 A B f s) (@I (A -> B) f x''''') t x h1). Qed.
Lemma lem5069511 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : term996 A B f x''''' t.
Proof. exact (@lem5069508 A B s f x''''' t x h2 (@lem5069504 A B x''' y s f x''''' t h1 h3 h4)). Qed.
Lemma lem5069512 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : term1120 A B f x''''' t.
Proof. exact (fun h0 : term998 A B f x''''' t => @lem5069511 A B x''' x y s f x''''' t h1 h2 h3 h4). Qed.
Lemma lem5069514 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069515 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term1120 A B f x''''' t) = (term996 A B f x''''' t).
Proof. exact (@lem5069514 (term996 A B f x''''' t)). Qed.
Lemma lem5069516 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : term996 A B f x''''' t.
Proof. exact (EQ_MP (@lem5069515 A B f x''''' t) (@lem5069512 A B x''' x y s f x''''' t h1 h2 h3 h4)). Qed.
Lemma lem5069519 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5069521 {A B : Type'} (f : A -> B) (x''''' : A) (t : B -> Prop) : (term998 A B f x''''' t) = (term1121 A B f x''''' t).
Proof. exact (@lem5069519 (term996 A B f x''''' t)). Qed.
Lemma lem5069524 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term999 A B s f x''''' t) : term1121 A B f x''''' t.
Proof. exact (EQ_MP (@lem5069521 A B f x''''' t) (@lem5068639 A B s f x''''' t h1)). Qed.
Lemma lem5069527 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : False.
Proof. exact (@lem5069524 A B s f x''''' t h4 (@lem5069516 A B x''' x y s f x''''' t h1 h2 h3 h4)). Qed.
Lemma lem5069528 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : term1122.
Proof. exact (fun h0 : ~ False => @lem5069527 A B x''' x y s f x''''' t h1 h2 h3 h4). Qed.
Lemma lem5069530 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5069531 : term1122 = False.
Proof. exact (@lem5069530 False). Qed.
Lemma lem5069532 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (y : A) (s : A -> Prop) (f : A -> B) (x''''' : A) (t : B -> Prop) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) (h4 : term999 A B s f x''''' t) : False.
Proof. exact (EQ_MP (@lem5069531) (@lem5069528 A B x''' x y s f x''''' t h1 h2 h3 h4)). Qed.
Lemma lem5070026 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term886 A x''''' s.
Proof. exact (proj1 (@lem5067441 A B s f x''''' y h1)). Qed.
Lemma lem5070027 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term1076 A x''''' s.
Proof. exact (fun h0 : term888 A x''''' s => @lem5070026 A B s f x''''' y h1). Qed.
Lemma lem5070029 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5070030 {A : Type'} (x''''' : A) (s : A -> Prop) : (term1076 A x''''' s) = (term886 A x''''' s).
Proof. exact (@lem5070029 (term886 A x''''' s)). Qed.
Lemma lem5070031 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term886 A x''''' s.
Proof. exact (EQ_MP (@lem5070030 A x''''' s) (@lem5070027 A B s f x''''' y h1)). Qed.
Lemma lem5070033 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term886 A y s.
Proof. exact (proj1 (@lem5067442 A B s f x''''' y h1)). Qed.
Lemma lem5070034 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term1076 A y s.
Proof. exact (fun h0 : term888 A y s => @lem5070033 A B s f x''''' y h1). Qed.
Lemma lem5070036 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5070037 {A : Type'} (y : A) (s : A -> Prop) : (term1076 A y s) = (term886 A y s).
Proof. exact (@lem5070036 (term886 A y s)). Qed.
Lemma lem5070038 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term886 A y s.
Proof. exact (EQ_MP (@lem5070037 A y s) (@lem5070034 A B s f x''''' y h1)). Qed.
Lemma lem5070040 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : (@I (A -> B) f x''''') = (@I (A -> B) f y).
Proof. exact (proj2 (@lem5067442 A B s f x''''' y h1)). Qed.
Lemma lem5070041 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term1123 A B x''''' f y.
Proof. exact (fun h0 : term1003 A B x''''' f y => @lem5070040 A B s f x''''' y h1). Qed.
Lemma lem5070043 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5070044 {A B : Type'} (x''''' : A) (f : A -> B) (y : A) : (term1123 A B x''''' f y) = ((@I (A -> B) f x''''') = (@I (A -> B) f y)).
Proof. exact (@lem5070043 ((@I (A -> B) f x''''') = (@I (A -> B) f y))). Qed.
Lemma lem5070045 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : (@I (A -> B) f x''''') = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem5070044 A B x''''' f y) (@lem5070041 A B s f x''''' y h1)). Qed.
Lemma lem5070061 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5070062 {A B : Type'} (f : A -> B) (s : A -> Prop) (_65033 : A) (_65034 : A) : (term1069 A B s f _65033 _65034) = (term1124 A B f s _65033 _65034).
Proof. exact (@lem5070061 (term1003 A B _65033 f _65034) (term888 A _65034 s) (_65033 = _65034)). Qed.
Lemma lem5070078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5070079 {A : Type'} (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1125 A s _65033 _65034) = (term1126 A _65033 _65034 s).
Proof. exact (@lem5070078 (_65033 = _65034) (term888 A _65034 s)). Qed.
Lemma lem5070087 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) : (term1127 A B _65033 f _65034) = (term1127 A B _65033 f _65034).
Proof. exact (eq_refl (term1127 A B _65033 f _65034)). Qed.
Lemma lem5070088 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1124 A B f s _65033 _65034) = (term1128 A B f _65033 _65034 s).
Proof. exact (MK_COMB (@lem5070087 A B _65033 f _65034) (@lem5070079 A _65033 _65034 s)). Qed.
Lemma lem5070092 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5070093 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1128 A B f _65033 _65034 s) = (term1129 A B _65033 f _65034 s).
Proof. exact (@lem5070092 (_65033 = _65034) (term1003 A B _65033 f _65034) (term888 A _65034 s)). Qed.
Lemma lem5070113 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1124 A B f s _65033 _65034) = (term1129 A B _65033 f _65034 s).
Proof. exact (TRANS (@lem5070088 A B f _65033 _65034 s) (@lem5070093 A B _65033 f _65034 s)). Qed.
Lemma lem5070114 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1069 A B s f _65033 _65034) = (term1129 A B _65033 f _65034 s).
Proof. exact (TRANS (@lem5070062 A B f s _65033 _65034) (@lem5070113 A B _65033 f _65034 s)). Qed.
Lemma lem5070115 {A : Type'} (_65033 : A) (s : A -> Prop) : (term889 A _65033 s) = (term889 A _65033 s).
Proof. exact (eq_refl (term889 A _65033 s)). Qed.
Lemma lem5070116 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1070 A B s f _65033 _65034) = (term1130 A B _65033 f _65034 s).
Proof. exact (MK_COMB (@lem5070115 A _65033 s) (@lem5070114 A B _65033 f _65034 s)). Qed.
Lemma lem5070120 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5070121 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1130 A B _65033 f _65034 s) = (term1131 A B _65033 f _65034 s).
Proof. exact (@lem5070120 (_65033 = _65034) (term888 A _65033 s) (term1132 A B _65033 f _65034 s)). Qed.
Lemma lem5070137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5070138 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1133 A B _65033 f _65034 s) = (term1134 A B f _65033 _65034 s).
Proof. exact (@lem5070137 (term1003 A B _65033 f _65034) (term888 A _65033 s) (term888 A _65034 s)). Qed.
Lemma lem5070156 {A : Type'} (_65033 : A) (_65034 : A) : (term1135 A _65033 _65034) = (term1135 A _65033 _65034).
Proof. exact (eq_refl (term1135 A _65033 _65034)). Qed.
Lemma lem5070157 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1131 A B _65033 f _65034 s) = (term1136 A B f _65033 _65034 s).
Proof. exact (MK_COMB (@lem5070156 A _65033 _65034) (@lem5070138 A B f _65033 _65034 s)). Qed.
Lemma lem5070168 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1130 A B _65033 f _65034 s) = (term1136 A B f _65033 _65034 s).
Proof. exact (TRANS (@lem5070121 A B _65033 f _65034 s) (@lem5070157 A B f _65033 _65034 s)). Qed.
Lemma lem5070169 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1070 A B s f _65033 _65034) = (term1136 A B f _65033 _65034 s).
Proof. exact (TRANS (@lem5070116 A B _65033 f _65034 s) (@lem5070168 A B f _65033 _65034 s)). Qed.
Lemma lem5070170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5070171 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1137 A B s f _65033 _65034) = (term1138 A B f _65033 _65034 s).
Proof. exact (MK_COMB (@lem5070170) (@lem5070169 A B f _65033 _65034 s)). Qed.
Lemma lem5070197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5070198 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1004 A B s _65033 f _65034) = (term1132 A B _65033 f _65034 s).
Proof. exact (@lem5070197 (term1003 A B _65033 f _65034) (term888 A _65034 s)). Qed.
Lemma lem5070206 {A : Type'} (_65033 : A) (s : A -> Prop) : (term889 A _65033 s) = (term889 A _65033 s).
Proof. exact (eq_refl (term889 A _65033 s)). Qed.
Lemma lem5070207 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) (s : A -> Prop) : (term1005 A B s _65033 f _65034) = (term1133 A B _65033 f _65034 s).
Proof. exact (MK_COMB (@lem5070206 A _65033 s) (@lem5070198 A B _65033 f _65034 s)). Qed.
Lemma lem5070211 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5070212 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1133 A B _65033 f _65034 s) = (term1134 A B f _65033 _65034 s).
Proof. exact (@lem5070211 (term1003 A B _65033 f _65034) (term888 A _65033 s) (term888 A _65034 s)). Qed.
Lemma lem5070230 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1005 A B s _65033 f _65034) = (term1134 A B f _65033 _65034 s).
Proof. exact (TRANS (@lem5070207 A B _65033 f _65034 s) (@lem5070212 A B f _65033 _65034 s)). Qed.
Lemma lem5070231 {A : Type'} (_65033 : A) (_65034 : A) : (term1135 A _65033 _65034) = (term1135 A _65033 _65034).
Proof. exact (eq_refl (term1135 A _65033 _65034)). Qed.
Lemma lem5070232 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : (term1139 A B s _65033 f _65034) = (term1136 A B f _65033 _65034 s).
Proof. exact (MK_COMB (@lem5070231 A _65033 _65034) (@lem5070230 A B f _65033 _65034 s)). Qed.
Lemma lem5070243 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : ((term1070 A B s f _65033 _65034) = (term1139 A B s _65033 f _65034)) = ((term1136 A B f _65033 _65034 s) = (term1136 A B f _65033 _65034 s)).
Proof. exact (MK_COMB (@lem5070171 A B f _65033 _65034 s) (@lem5070232 A B f _65033 _65034 s)). Qed.
Lemma lem5070245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5070246 (x : Prop) : (x = x) = True.
Proof. exact (@lem5070245 Prop x). Qed.
Lemma lem5070247 {A B : Type'} (f : A -> B) (_65033 : A) (_65034 : A) (s : A -> Prop) : ((term1136 A B f _65033 _65034 s) = (term1136 A B f _65033 _65034 s)) = True.
Proof. exact (@lem5070246 (term1136 A B f _65033 _65034 s)). Qed.
Lemma lem5070248 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : ((term1070 A B s f _65033 _65034) = (term1139 A B s _65033 f _65034)) = True.
Proof. exact (TRANS (@lem5070243 A B f _65033 _65034 s) (@lem5070247 A B f _65033 _65034 s)). Qed.
Lemma lem5070249 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : True = ((term1070 A B s f _65033 _65034) = (term1139 A B s _65033 f _65034)).
Proof. exact (SYM (@lem5070248 A B s _65033 f _65034)). Qed.
Lemma lem5070250 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1070 A B s f _65033 _65034) = (term1139 A B s _65033 f _65034).
Proof. exact (EQ_MP (@lem5070249 A B s _65033 f _65034) (@lem0)). Qed.
Lemma lem5070251 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1139 A B s _65033 f _65034.
Proof. exact (EQ_MP (@lem5070250 A B s _65033 f _65034) (@lem5068719 A B _65033 _65034 t s f x''''' y h1)). Qed.
Lemma lem5070253 (b : Prop) (a : Prop) : (a \/ b) = (term1077 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5070254 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1139 A B s _65033 f _65034) = (term1140 A B s f _65033 _65034).
Proof. exact (@lem5070253 (term1005 A B s _65033 f _65034) (_65033 = _65034)). Qed.
Lemma lem5070256 (a : Prop) (b : Prop) : (term1079 a b) = (term1080 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5070257 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1141 A B s _65033 f _65034) = (term1142 A B s _65033 f _65034).
Proof. exact (@lem5070256 (term888 A _65033 s) (term1004 A B s _65033 f _65034)). Qed.
Lemma lem5070259 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5070260 {A : Type'} (_65033 : A) (s : A -> Prop) : (term1087 A _65033 s) = (term886 A _65033 s).
Proof. exact (@lem5070259 (term886 A _65033 s)). Qed.
Lemma lem5070261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070262 {A : Type'} (_65033 : A) (s : A -> Prop) : (term1143 A _65033 s) = (term985 A _65033 s).
Proof. exact (MK_COMB (@lem5070261) (@lem5070260 A _65033 s)). Qed.
Lemma lem5070264 (a : Prop) (b : Prop) : (term1079 a b) = (term1080 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5070265 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1144 A B s _65033 f _65034) = (term1145 A B s _65033 f _65034).
Proof. exact (@lem5070264 (term888 A _65034 s) (term1003 A B _65033 f _65034)). Qed.
Lemma lem5070267 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5070268 {A : Type'} (_65034 : A) (s : A -> Prop) : (term1087 A _65034 s) = (term886 A _65034 s).
Proof. exact (@lem5070267 (term886 A _65034 s)). Qed.
Lemma lem5070269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070270 {A : Type'} (_65034 : A) (s : A -> Prop) : (term1143 A _65034 s) = (term985 A _65034 s).
Proof. exact (MK_COMB (@lem5070269) (@lem5070268 A _65034 s)). Qed.
Lemma lem5070272 (a : Prop) : (term1083 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5070273 {A B : Type'} (_65033 : A) (f : A -> B) (_65034 : A) : (term1146 A B _65033 f _65034) = ((@I (A -> B) f _65033) = (@I (A -> B) f _65034)).
Proof. exact (@lem5070272 ((@I (A -> B) f _65033) = (@I (A -> B) f _65034))). Qed.
Lemma lem5070274 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1145 A B s _65033 f _65034) = (term986 A B s _65033 f _65034).
Proof. exact (MK_COMB (@lem5070270 A _65034 s) (@lem5070273 A B _65033 f _65034)). Qed.
Lemma lem5070275 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1144 A B s _65033 f _65034) = (term986 A B s _65033 f _65034).
Proof. exact (TRANS (@lem5070265 A B s _65033 f _65034) (@lem5070274 A B s _65033 f _65034)). Qed.
Lemma lem5070276 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1142 A B s _65033 f _65034) = (term987 A B s _65033 f _65034).
Proof. exact (MK_COMB (@lem5070262 A _65033 s) (@lem5070275 A B s _65033 f _65034)). Qed.
Lemma lem5070277 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1141 A B s _65033 f _65034) = (term987 A B s _65033 f _65034).
Proof. exact (TRANS (@lem5070257 A B s _65033 f _65034) (@lem5070276 A B s _65033 f _65034)). Qed.
Lemma lem5070278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070279 {A B : Type'} (s : A -> Prop) (_65033 : A) (f : A -> B) (_65034 : A) : (term1147 A B s _65033 f _65034) = (term1148 A B s _65033 f _65034).
Proof. exact (MK_COMB (@lem5070278) (@lem5070277 A B s _65033 f _65034)). Qed.
Lemma lem5070280 {A : Type'} (_65033 : A) (_65034 : A) : (_65033 = _65034) = (_65033 = _65034).
Proof. exact (eq_refl (_65033 = _65034)). Qed.
Lemma lem5070281 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1140 A B s f _65033 _65034) = (term1149 A B s f _65033 _65034).
Proof. exact (MK_COMB (@lem5070279 A B s _65033 f _65034) (@lem5070280 A _65033 _65034)). Qed.
Lemma lem5070282 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65033 : A) (_65034 : A) : (term1139 A B s _65033 f _65034) = (term1149 A B s f _65033 _65034).
Proof. exact (TRANS (@lem5070254 A B s f _65033 _65034) (@lem5070281 A B s f _65033 _65034)). Qed.
Lemma lem5070284 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term986 A B s x''''' f y.
Proof. exact (conj (@lem5070038 A B s f x''''' y h1) (@lem5070045 A B s f x''''' y h1)). Qed.
Lemma lem5070285 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term987 A B s x''''' f y.
Proof. exact (conj (@lem5070031 A B s f x''''' y h1) (@lem5070284 A B s f x''''' y h1)). Qed.
Lemma lem5070287 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1149 A B s f _65033 _65034.
Proof. exact (EQ_MP (@lem5070282 A B s f _65033 _65034) (@lem5070251 A B _65033 _65034 t s f x''''' y h1)). Qed.
Lemma lem5070288 {A B : Type'} (_65033 : A) (_65034 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1149 A B s f _65033 _65034.
Proof. exact (@lem5070287 A B _65033 _65034 t s f x''''' y h1). Qed.
Lemma lem5070289 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term335 A B t s f x''''' y) : term1149 A B s f x''''' y.
Proof. exact (@lem5070288 A B x''''' y t s f x''''' y h1). Qed.
Lemma lem5070292 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : x''''' = y.
Proof. exact (@lem5070289 A B t s f x''''' y h2 (@lem5070285 A B s f x''''' y h1)). Qed.
Lemma lem5070293 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : term1150 A x''''' y.
Proof. exact (fun h0 : term981 A x''''' y => @lem5070292 A B t s f x''''' y h1 h2). Qed.
Lemma lem5070295 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5070296 {A : Type'} (x''''' : A) (y : A) : (term1150 A x''''' y) = (x''''' = y).
Proof. exact (@lem5070295 (x''''' = y)). Qed.
Lemma lem5070297 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : x''''' = y.
Proof. exact (EQ_MP (@lem5070296 A x''''' y) (@lem5070293 A B t s f x''''' y h1 h2)). Qed.
Lemma lem5070300 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5070302 {A : Type'} (x''''' : A) (y : A) : (term981 A x''''' y) = (term1151 A x''''' y).
Proof. exact (@lem5070300 (x''''' = y)). Qed.
Lemma lem5070305 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) : term1151 A x''''' y.
Proof. exact (EQ_MP (@lem5070302 A x''''' y) (@lem5068771 A B s f x''''' y h1)). Qed.
Lemma lem5070308 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : False.
Proof. exact (@lem5070305 A B s f x''''' y h1 (@lem5070297 A B t s f x''''' y h1 h2)). Qed.
Lemma lem5070309 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : term1122.
Proof. exact (fun h0 : ~ False => @lem5070308 A B t s f x''''' y h1 h2). Qed.
Lemma lem5070311 (p : Prop) : (term1073 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5070312 : term1122 = False.
Proof. exact (@lem5070311 False). Qed.
Lemma lem5070313 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term990 A B s f x''''' y) (h2 : term335 A B t s f x''''' y) : False.
Proof. exact (EQ_MP (@lem5070312) (@lem5070309 A B t s f x''''' y h1 h2)). Qed.
Lemma lem5070314 {A B : Type'} (x''' : type1448 A B) (x : type638 B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (y : A) (h1 : term731 A B x''') (h2 : term882 B x) (h3 : term335 A B t s f x''''' y) : False.
Proof. exact (or_elim (@lem5067422 A B t s f x''''' y h3) (fun h0 : term999 A B s f x''''' t => @lem5069532 A B x''' x y s f x''''' t h1 h2 h3 h0) (fun h0 : term990 A B s f x''''' y => @lem5070313 A B t s f x''''' y h0 h3)). Qed.
Lemma lem5070315 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''''' : A) (x''' : type1448 A B) (x : type638 B) (h1 : term338 A B t s f x''''') (h2 : term731 A B x''') (h3 : term882 B x) : False.
Proof. exact (ex_elim (@lem5066194 A B t s f x''''' h1) (fun y : A => fun h0 : term337 A B t s f x''''' y => @lem5070314 A B x''' x t s f x''''' y h2 h3 h0)). Qed.
Lemma lem5070316 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x''' : type1448 A B) (x : type638 B) (h1 : term340 A B t s f) (h2 : term731 A B x''') (h3 : term882 B x) : False.
Proof. exact (ex_elim (@lem5066193 A B t s f h1) (fun x''''' : A => fun h0 : term339 A B t s f x''''' => @lem5070315 A B t s f x''''' x''' x h0 h2 h3)). Qed.
Lemma lem5070317 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x''' : type1448 A B) (x : type638 B) (h1 : term147 A B t s) (h2 : term731 A B x''') (h3 : term882 B x) : False.
Proof. exact (ex_elim (@lem5062271 A B t s h1) (fun f : A -> B => fun h0 : term341 A B t s f => @lem5070316 A B t s f x''' x h0 h2 h3)). Qed.
Lemma lem5070318 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x''' : type1448 A B) (x : type638 B) (h1 : term149 A) (h2 : term147 A B t s) (h3 : term731 A B x''') (h4 : term882 B x) : False.
Proof. exact (ex_elim (@lem5063163 A h1) (fun x'''' : type1361 A => fun h0 : term541 A x'''' => @lem5070317 A B t s x''' x h2 h3 h4)). Qed.
Lemma lem5070319 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : type638 B) (h1 : term149 A) (h2 : term150 A B) (h3 : term147 A B t s) (h4 : term882 B x) : False.
Proof. exact (ex_elim (@lem5064055 A B h2) (fun x''' : type1448 A B => fun h0 : term733 A B x''' => @lem5070318 A B t s x''' x h1 h3 h0 h4)). Qed.
Lemma lem5070320 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : type638 B) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term147 A B t s) (h5 : term882 B x) : False.
Proof. exact (ex_elim (@lem5064947 B h3) (fun x'' : type1361 B => fun h0 : term541 B x'' => @lem5070319 A B t s x h1 h2 h4 h5)). Qed.
Lemma lem5070321 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : type638 B) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term148 A) (h5 : term147 A B t s) (h6 : term882 B x) : False.
Proof. exact (ex_elim (@lem5065567 A h4) (fun x' : type638 A => fun h0 : term884 A x' => @lem5070320 A B t s x h1 h2 h3 h5 h6)). Qed.
Lemma lem5070322 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term148 A) (h5 : term148 B) (h6 : term147 A B t s) : False.
Proof. exact (ex_elim (@lem5066187 B h5) (fun x : type638 B => fun h0 : term884 B x => @lem5070321 A B t s x h1 h2 h3 h4 h6 h0)). Qed.
Lemma lem5070323 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term148 A) (h5 : term147 A B t s) : term155 B.
Proof. exact (fun h0 : term148 B => @lem5070322 A B t s h1 h2 h3 h4 h0 h5). Qed.
Lemma lem5070324 {B : Type'} : (term155 B) = (term156 B).
Proof. exact (@lem69 (term148 B)). Qed.
Lemma lem5070325 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term148 A) (h5 : term147 A B t s) : term156 B.
Proof. exact (EQ_MP (@lem5070324 B) (@lem5070323 A B t s h1 h2 h3 h4 h5)). Qed.
Lemma lem5070326 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term150 A B) (h3 : term149 B) (h4 : term147 A B t s) : term159 A B.
Proof. exact (fun h0 : term148 A => @lem5070325 A B t s h1 h2 h3 h0 h4). Qed.
Lemma lem5070327 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term150 A B) (h3 : term147 A B t s) : term162 A B.
Proof. exact (fun h0 : term149 B => @lem5070326 A B t s h1 h2 h0 h3). Qed.
Lemma lem5070328 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A) (h2 : term147 A B t s) : term165 A B.
Proof. exact (fun h0 : term150 A B => @lem5070327 A B t s h1 h0 h2). Qed.
Lemma lem5070329 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term167 A B.
Proof. exact (fun h0 : term149 A => @lem5070328 A B t s h0 h1). Qed.
Lemma lem5070330 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term169 A B t s.
Proof. exact (fun h0 : term147 A B t s => @lem5070329 A B t s h0). Qed.
Lemma lem5070335 {A B : Type'} (s : A -> Prop) : term173 A B s.
Proof. exact (fun t : B -> Prop => @lem5070330 A B t s). Qed.
Lemma lem5070340 {A B : Type'} : term177 A B.
Proof. exact (fun s : A -> Prop => @lem5070335 A B s). Qed.
Lemma lem5070341 {A B : Type'} : term176 A B.
Proof. exact (EQ_MP (@lem5061859 A B) (@lem5070340 A B)). Qed.
Lemma lem5070342 {A B : Type'} (s : A -> Prop) : term1152 A B s.
Proof. exact (@lem5070341 A B s). Qed.
Lemma lem5070343 {A B : Type'} (s : A -> Prop) : (term1152 A B s) = (term172 A B s).
Proof. exact (eq_refl (term1152 A B s)). Qed.
Lemma lem5070344 {A B : Type'} (s : A -> Prop) : term172 A B s.
Proof. exact (EQ_MP (@lem5070343 A B s) (@lem5070342 A B s)). Qed.
Lemma lem5070345 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term1153 A B s t.
Proof. exact (@lem5070344 A B s t). Qed.
Lemma lem5070346 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term1153 A B s t) = (term151 A B t s).
Proof. exact (eq_refl (term1153 A B s t)). Qed.
Lemma lem5070347 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term151 A B t s.
Proof. exact (EQ_MP (@lem5070346 A B t s) (@lem5070345 A B s t)). Qed.
Lemma lem5070349 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term151 A B t s.
Proof. exact (@lem5061159 A B t s (@lem5070347 A B t s)). Qed.
Lemma lem5070350 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term166 A B.
Proof. exact (@lem5070349 A B t s (@lem5061133 A B t s h1)). Qed.
Lemma lem5070351 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term164 A B.
Proof. exact (@lem5070350 A B t s h1 (@lem5061137 A)). Qed.
Lemma lem5070352 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term161 A B.
Proof. exact (@lem5070351 A B t s h1 (@lem5061138 A B)). Qed.
Lemma lem5070353 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term158 A B.
Proof. exact (@lem5070352 A B t s h1 (@lem5061143 B)). Qed.
Lemma lem5070354 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : term155 B.
Proof. exact (@lem5070353 A B t s h1 (@lem5061135 A)). Qed.
Lemma lem5070355 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : False.
Proof. exact (@lem5070354 A B t s h1 (@lem5061134 B)). Qed.
Lemma lem5070356 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : (term147 A B t s) = False.
Proof. exact (prop_ext (fun h2 : term147 A B t s => @lem5070355 A B t s h1) (fun h2 : False => @lem5061133 A B t s h1)). Qed.
Lemma lem5070357 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term147 A B t s) : False.
Proof. exact (EQ_MP (@lem5070356 A B t s h1) (@lem5061133 A B t s h1)). Qed.
Lemma lem5070358 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term146 A B t s.
Proof. exact (fun h0 : term147 A B t s => @lem5070357 A B t s h0). Qed.
Lemma lem5070359 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term144 A B t s.
Proof. exact (EQ_MP (@lem5061132 A B t s) (@lem5070358 A B t s)). Qed.
Lemma lem5070360 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term100 A B t s.
Proof. exact (EQ_MP (@lem5061128 A B s t h1 h2 h3) (@lem5070359 A B t s)). Qed.
Lemma lem5070361 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term84 A B t s.
Proof. exact (@lem5056705 A B t s (@lem5070360 A B s t h1 h2 h3)). Qed.
Lemma lem5070362 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term83 A B t s.
Proof. exact (EQ_MP (@lem5056678 A B s t h1 h2 h3) (@lem5070361 A B s t h1 h2 h3)). Qed.
Lemma lem5070363 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term49 A B t s) : term82 A B t s.
Proof. exact (@lem5070362 A B s t h1 h2 h3 (@lem5056517 A B t s h4)). Qed.
Lemma lem5070364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term69 A B s t) : term70 A B s t.
Proof. exact (proj2 (@lem5056518 A B s t h1)). Qed.
Lemma lem5070365 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term69 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem5056518 A B s t h1)). Qed.
Lemma lem5070366 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term70 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (proj2 (@lem5056519 A B s t h1)). Qed.
Lemma lem5070367 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term70 A B s t) : @FINITE B t.
Proof. exact (proj1 (@lem5056519 A B s t h1)). Qed.
Lemma lem5070368 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term49 A B t s) : ((@CARD A s) = (@CARD B t)) = (term82 A B t s).
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (@CARD B t) => @lem5070363 A B t s h1 h2 h3 h4) (fun h5 : term82 A B t s => @lem5056521 A B s t h3)). Qed.
Lemma lem5070369 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070368 A B t s h1 h2 h3 h4) (@lem5056521 A B s t h3)). Qed.
Lemma lem5070370 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term49 A B t s) : (@FINITE B t) = (term82 A B t s).
Proof. exact (prop_ext (fun h5 : @FINITE B t => @lem5070369 A B t s h1 h2 h3 h4) (fun h5 : term82 A B t s => @lem5056522 B t h2)). Qed.
Lemma lem5070371 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070370 A B t s h1 h2 h3 h4) (@lem5056522 B t h2)). Qed.
Lemma lem5070372 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term70 A B s t) (h4 : term49 A B t s) : ((@CARD A s) = (@CARD B t)) = (term82 A B t s).
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (@CARD B t) => @lem5070371 A B t s h1 h2 h5 h4) (fun h5 : term82 A B t s => @lem5070366 A B s t h3)). Qed.
Lemma lem5070373 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term70 A B s t) (h4 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070372 A B t s h1 h2 h3 h4) (@lem5070366 A B s t h3)). Qed.
Lemma lem5070374 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term70 A B s t) (h3 : term49 A B t s) : (@FINITE B t) = (term82 A B t s).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem5070373 A B t s h1 h4 h2 h3) (fun h4 : term82 A B t s => @lem5070367 A B s t h2)). Qed.
Lemma lem5070375 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term70 A B s t) (h3 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070374 A B t s h1 h2 h3) (@lem5070367 A B s t h2)). Qed.
Lemma lem5070376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term70 A B s t) (h3 : term49 A B t s) : (@FINITE A s) = (term82 A B t s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem5070375 A B t s h1 h2 h3) (fun h4 : term82 A B t s => @lem5056520 A s h1)). Qed.
Lemma lem5070377 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term70 A B s t) (h3 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070376 A B t s h1 h2 h3) (@lem5056520 A s h1)). Qed.
Lemma lem5070378 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term69 A B s t) (h3 : term49 A B t s) : (term70 A B s t) = (term82 A B t s).
Proof. exact (prop_ext (fun h4 : term70 A B s t => @lem5070377 A B t s h1 h4 h3) (fun h4 : term82 A B t s => @lem5070364 A B s t h2)). Qed.
Lemma lem5070379 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term69 A B s t) (h3 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070378 A B t s h1 h2 h3) (@lem5070364 A B s t h2)). Qed.
Lemma lem5070380 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term69 A B s t) (h2 : term49 A B t s) : (@FINITE A s) = (term82 A B t s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem5070379 A B t s h3 h1 h2) (fun h3 : term82 A B t s => @lem5070365 A B s t h1)). Qed.
Lemma lem5070381 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term69 A B s t) (h2 : term49 A B t s) : term82 A B t s.
Proof. exact (EQ_MP (@lem5070380 A B t s h1 h2) (@lem5070365 A B s t h1)). Qed.
Lemma lem5070382 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term49 A B t s) : term53 A B t s.
Proof. exact (fun h0 : term69 A B s t => @lem5070381 A B t s h0 h1). Qed.
Lemma lem5070383 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term55 A B t s.
Proof. exact (fun h0 : term49 A B t s => @lem5070382 A B t s h0). Qed.
Lemma lem5070388 {A B : Type'} (s : A -> Prop) : term59 A B s.
Proof. exact (fun t : B -> Prop => @lem5070383 A B t s). Qed.
Lemma lem5070389 {A B : Type'} (s : A -> Prop) : term27 A B s.
Proof. exact (@lem5056514 A B s (@lem5070388 A B s)). Qed.
Lemma lem5070394 {A B : Type'} : term31 A B.
Proof. exact (fun s : A -> Prop => @lem5070389 A B s). Qed.
Lemma lem5070395 {A B : Type'} : term43 A B.
Proof. exact (@lem5056487 A B (@lem5070394 A B)). Qed.
Lemma lem5070396 {A B : Type'} : term41 A B.
Proof. exact (@lem5070395 A B (@lem5029861 A B)). Qed.
