Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1052523_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm1052197_spec.
Require Import thm1052447_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1052448 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem1052449 : term1.
Proof. exact (EQ_MP (@lem1052448) (@lem1052197)). Qed.
Lemma lem1052450 : term2.
Proof. exact (@lem1052449 term3). Qed.
Lemma lem1052451 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem1052452 : term4.
Proof. exact (EQ_MP (@lem1052451) (@lem1052450)). Qed.
Lemma lem1052453 (h1 : NUMFST = term5) : NUMFST = term5.
Proof. exact (h1). Qed.
Lemma lem1052454 (h1 : NUMFST = term5) : term5 = NUMFST.
Proof. exact (SYM (@lem1052453 h1)). Qed.
Lemma lem1052455 (h1 : term5 = NUMFST) : term5 = NUMFST.
Proof. exact (h1). Qed.
Lemma lem1052456 (h1 : term5 = NUMFST) : NUMFST = term5.
Proof. exact (SYM (@lem1052455 h1)). Qed.
Lemma lem1052457 : (NUMFST = term5) = (term5 = NUMFST).
Proof. exact (prop_ext (fun h1 : NUMFST = term5 => @lem1052454 h1) (fun h1 : term5 = NUMFST => @lem1052456 h1)). Qed.
Lemma lem1052460 : term5 = NUMFST.
Proof. exact (EQ_MP (@lem1052457) (@lem1052447)). Qed.
Lemma lem1052461 (x : nat) (y : nat) : (NUMPAIR x y) = (NUMPAIR x y).
Proof. exact (eq_refl (NUMPAIR x y)). Qed.
Lemma lem1052462 (x : nat) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1052460) (@lem1052461 x y)). Qed.
Lemma lem1052463 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1052464 (x : nat) (y : nat) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1052463) (@lem1052462 x y)). Qed.
Lemma lem1052465 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1052466 (y : nat) (x : nat) : ((term6 x y) = x) = ((term7 x y) = x).
Proof. exact (MK_COMB (@lem1052464 x y) (@lem1052465 x)). Qed.
Lemma lem1052467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1052468 (y : nat) (x : nat) : (term10 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1052467) (@lem1052466 y x)). Qed.
Lemma lem1052469 (Y : nat -> nat) (x : nat) (y : nat) : ((term12 Y x y) = y) = ((term12 Y x y) = y).
Proof. exact (eq_refl ((term12 Y x y) = y)). Qed.
Lemma lem1052470 (Y : nat -> nat) (x : nat) (y : nat) : (term13 Y x y) = (term14 Y x y).
Proof. exact (MK_COMB (@lem1052468 y x) (@lem1052469 Y x y)). Qed.
Lemma lem1052471 (Y : nat -> nat) (x : nat) : (term15 Y x) = (term16 Y x).
Proof. exact (fun_ext (fun y : nat => @lem1052470 Y x y)). Qed.
Lemma lem1052472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1052473 (Y : nat -> nat) (x : nat) : (term17 Y x) = (term18 Y x).
Proof. exact (MK_COMB (@lem1052472) (@lem1052471 Y x)). Qed.
Lemma lem1052474 (Y : nat -> nat) : (term19 Y) = (term20 Y).
Proof. exact (fun_ext (fun x : nat => @lem1052473 Y x)). Qed.
Lemma lem1052475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1052476 (Y : nat -> nat) : (term21 Y) = (term22 Y).
Proof. exact (MK_COMB (@lem1052475) (@lem1052474 Y)). Qed.
Lemma lem1052477 : term23 = term24.
Proof. exact (fun_ext (fun Y : nat -> nat => @lem1052476 Y)). Qed.
Lemma lem1052478 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1052479 : term4 = term25.
Proof. exact (MK_COMB (@lem1052478) (@lem1052477)). Qed.
Lemma lem1052480 : term25.
Proof. exact (EQ_MP (@lem1052479) (@lem1052452)). Qed.
Lemma lem1052481 : term26.
Proof. exact (fun _17341 : type1671 => @lem1052480). Qed.
Lemma lem1052482 {A B : Type'} (P : type1413 A B) : term27 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1052483 {A B : Type'} (P : type1413 A B) : (term27 A B P) = ((term28 A B P) = (term29 A B P)).
Proof. exact (eq_refl (term27 A B P)). Qed.
Lemma lem1052486 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem1052483 A B P) (@lem1052482 A B P)). Qed.
Lemma lem1052487 (P : type1269) : (term30 P) = (term31 P).
Proof. exact (@lem1052486 type1671 (nat -> nat) P). Qed.
Lemma lem1052488 : term32 = term33.
Proof. exact (@lem1052487 term34). Qed.
Lemma lem1052489 (_17341 : type1671) : (term35 _17341) = term24.
Proof. exact (eq_refl (term35 _17341)). Qed.
Lemma lem1052490 (Y : nat -> nat) : Y = Y.
Proof. exact (eq_refl Y). Qed.
Lemma lem1052491 (_17341 : type1671) (Y : nat -> nat) : (term36 _17341 Y) = (term37 Y).
Proof. exact (MK_COMB (@lem1052489 _17341) (@lem1052490 Y)). Qed.
Lemma lem1052492 (Y : nat -> nat) : (term37 Y) = (term22 Y).
Proof. exact (eq_refl (term37 Y)). Qed.
Lemma lem1052493 (_17341 : type1671) (Y : nat -> nat) : (term36 _17341 Y) = (term22 Y).
Proof. exact (TRANS (@lem1052491 _17341 Y) (@lem1052492 Y)). Qed.
Lemma lem1052494 (_17341 : type1671) : (term38 _17341) = term24.
Proof. exact (fun_ext (fun Y : nat -> nat => @lem1052493 _17341 Y)). Qed.
Lemma lem1052495 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1052496 (_17341 : type1671) : (term39 _17341) = term25.
Proof. exact (MK_COMB (@lem1052495) (@lem1052494 _17341)). Qed.
Lemma lem1052497 : term40 = term41.
Proof. exact (fun_ext (fun _17341 : type1671 => @lem1052496 _17341)). Qed.
Lemma lem1052498 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1052499 : term32 = term26.
Proof. exact (MK_COMB (@lem1052498) (@lem1052497)). Qed.
Lemma lem1052500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1052501 : term42 = term43.
Proof. exact (MK_COMB (@lem1052500) (@lem1052499)). Qed.
Lemma lem1052502 (_17341 : type1671) : (term35 _17341) = term24.
Proof. exact (eq_refl (term35 _17341)). Qed.
Lemma lem1052503 (Y : type1272) (_17341 : type1671) : (Y _17341) = (Y _17341).
Proof. exact (eq_refl (Y _17341)). Qed.
Lemma lem1052504 (Y : type1272) (_17341 : type1671) : (term44 Y _17341) = (term45 Y _17341).
Proof. exact (MK_COMB (@lem1052502 _17341) (@lem1052503 Y _17341)). Qed.
Lemma lem1052505 (Y : type1272) (_17341 : type1671) : (term45 Y _17341) = (term46 Y _17341).
Proof. exact (eq_refl (term45 Y _17341)). Qed.
Lemma lem1052506 (Y : type1272) (_17341 : type1671) : (term44 Y _17341) = (term46 Y _17341).
Proof. exact (TRANS (@lem1052504 Y _17341) (@lem1052505 Y _17341)). Qed.
Lemma lem1052507 (Y : type1272) : (term47 Y) = (term48 Y).
Proof. exact (fun_ext (fun _17341 : type1671 => @lem1052506 Y _17341)). Qed.
Lemma lem1052508 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1052509 (Y : type1272) : (term49 Y) = (term50 Y).
Proof. exact (MK_COMB (@lem1052508) (@lem1052507 Y)). Qed.
Lemma lem1052510 : term51 = term52.
Proof. exact (fun_ext (fun Y : type1272 => @lem1052509 Y)). Qed.
Lemma lem1052511 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat))). Qed.
Lemma lem1052512 : term33 = term53.
Proof. exact (MK_COMB (@lem1052511) (@lem1052510)). Qed.
Lemma lem1052513 : (term32 = term33) = (term26 = term53).
Proof. exact (MK_COMB (@lem1052501) (@lem1052512)). Qed.
Lemma lem1052514 : term26 = term53.
Proof. exact (EQ_MP (@lem1052513) (@lem1052488)). Qed.
Lemma lem1052515 : term53.
Proof. exact (EQ_MP (@lem1052514) (@lem1052481)). Qed.
Lemma lem1052517 {A : Type'} : (@ex A) = (term54 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1052518 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)) = term55.
Proof. exact (@lem1052517 type1272). Qed.
Lemma lem1052519 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1052520 : term53 = term56.
Proof. exact (MK_COMB (@lem1052518) (@lem1052519)). Qed.
Lemma lem1052521 : term56 = term57.
Proof. exact (eq_refl term56). Qed.
Lemma lem1052522 : term53 = term57.
Proof. exact (TRANS (@lem1052520) (@lem1052521)). Qed.
Lemma lem1052523 : term57.
Proof. exact (EQ_MP (@lem1052522) (@lem1052515)). Qed.
