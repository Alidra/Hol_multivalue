Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3789889_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem3789426 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem3789427 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem3789428 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3789427 A B f) (@lem3789426 A B f)). Qed.
Lemma lem3789429 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem3789428 A B f y). Qed.
Lemma lem3789430 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem3789433 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : FINREC' = (term4 A B _43482).
Proof. exact (h1). Qed.
Lemma lem3789434 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789435 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789433 A B FINREC' _43482 h1) (@lem3789434 A B f)). Qed.
Lemma lem3789437 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789438 {A B : Type'} (f : type431 A B) (y : type1411 A B) : (term6 A B f y) = (f y).
Proof. exact (@lem3789437 (type1411 A B) (type1449 A B) f y). Qed.
Lemma lem3789439 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (@lem3789438 A B (term4 A B _43482) f). Qed.
Lemma lem3789440 {A B : Type'} (_43482 : type1570 A B) (_43477 : type1411 A B) : (term5 A B _43482 _43477) = (term8 A B _43482 _43477).
Proof. exact (eq_refl (term5 A B _43482 _43477)). Qed.
Lemma lem3789441 {A B : Type'} (_43482 : type1570 A B) : (term9 A B _43482) = (term4 A B _43482).
Proof. exact (fun_ext (fun _43477 : type1411 A B => @lem3789440 A B _43482 _43477)). Qed.
Lemma lem3789442 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789443 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789441 A B _43482) (@lem3789442 A B f)). Qed.
Lemma lem3789444 {A B : Type'} : (@eq (B -> (A -> Prop) -> B -> nat -> Prop)) = (@eq (B -> (A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> (A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789445 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term10 A B _43482 f) = (term11 A B _43482 f).
Proof. exact (MK_COMB (@lem3789444 A B) (@lem3789443 A B _43482 f)). Qed.
Lemma lem3789446 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (eq_refl (term5 A B _43482 f)). Qed.
Lemma lem3789447 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : ((term7 A B _43482 f) = (term5 A B _43482 f)) = ((term5 A B _43482 f) = (term8 A B _43482 f)).
Proof. exact (MK_COMB (@lem3789445 A B _43482 f) (@lem3789446 A B _43482 f)). Qed.
Lemma lem3789448 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (EQ_MP (@lem3789447 A B _43482 f) (@lem3789439 A B _43482 f)). Qed.
Lemma lem3789449 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term8 A B _43482 f).
Proof. exact (TRANS (@lem3789435 A B f FINREC' _43482 h1) (@lem3789448 A B _43482 f)). Qed.
Lemma lem3789450 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789451 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789449 A B f FINREC' _43482 h1) (@lem3789450 B b)). Qed.
Lemma lem3789453 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789454 {A B : Type'} (f : type1449 A B) (y : B) : (term13 A B f y) = (f y).
Proof. exact (@lem3789453 B (type676 A B) f y). Qed.
Lemma lem3789455 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (@lem3789454 A B (term8 A B _43482 f) b). Qed.
Lemma lem3789456 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (_43478 : B) : (term12 A B _43482 f _43478) = (term15 A B _43482 f _43478).
Proof. exact (eq_refl (term12 A B _43482 f _43478)). Qed.
Lemma lem3789457 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term16 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (fun_ext (fun _43478 : B => @lem3789456 A B _43482 f _43478)). Qed.
Lemma lem3789458 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789459 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789457 A B _43482 f) (@lem3789458 B b)). Qed.
Lemma lem3789460 {A B : Type'} : (@eq ((A -> Prop) -> B -> nat -> Prop)) = (@eq ((A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789461 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term17 A B _43482 f b) = (term18 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789460 A B) (@lem3789459 A B _43482 f b)). Qed.
Lemma lem3789462 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (eq_refl (term12 A B _43482 f b)). Qed.
Lemma lem3789463 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : ((term14 A B _43482 f b) = (term12 A B _43482 f b)) = ((term12 A B _43482 f b) = (term15 A B _43482 f b)).
Proof. exact (MK_COMB (@lem3789461 A B _43482 f b) (@lem3789462 A B _43482 f b)). Qed.
Lemma lem3789464 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (EQ_MP (@lem3789463 A B _43482 f b) (@lem3789455 A B _43482 f b)). Qed.
Lemma lem3789465 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term15 A B _43482 f b).
Proof. exact (TRANS (@lem3789451 A B f b FINREC' _43482 h1) (@lem3789464 A B _43482 f b)). Qed.
Lemma lem3789466 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789467 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s) = (term19 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789465 A B f b FINREC' _43482 h1) (@lem3789466 A s)). Qed.
Lemma lem3789469 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789470 {A B : Type'} (f : type676 A B) (y : A -> Prop) : (term20 A B f y) = (f y).
Proof. exact (@lem3789469 (A -> Prop) (type1424 B) f y). Qed.
Lemma lem3789471 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term21 A B _43482 f b s) = (term19 A B _43482 f b s).
Proof. exact (@lem3789470 A B (term15 A B _43482 f b) s). Qed.
Lemma lem3789472 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (_43479 : A -> Prop) : (term19 A B _43482 f b _43479) = (term22 A B _43482 f b _43479).
Proof. exact (eq_refl (term19 A B _43482 f b _43479)). Qed.
Lemma lem3789473 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term23 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (fun_ext (fun _43479 : A -> Prop => @lem3789472 A B _43482 f b _43479)). Qed.
Lemma lem3789474 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789475 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term21 A B _43482 f b s) = (term19 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789473 A B _43482 f b) (@lem3789474 A s)). Qed.
Lemma lem3789476 {B : Type'} : (@eq (B -> nat -> Prop)) = (@eq (B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> nat -> Prop))). Qed.
Lemma lem3789477 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term24 A B _43482 f b s) = (term25 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789476 B) (@lem3789475 A B _43482 f b s)). Qed.
Lemma lem3789478 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term19 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (eq_refl (term19 A B _43482 f b s)). Qed.
Lemma lem3789479 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : ((term21 A B _43482 f b s) = (term19 A B _43482 f b s)) = ((term19 A B _43482 f b s) = (term22 A B _43482 f b s)).
Proof. exact (MK_COMB (@lem3789477 A B _43482 f b s) (@lem3789478 A B _43482 f b s)). Qed.
Lemma lem3789480 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term19 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (EQ_MP (@lem3789479 A B _43482 f b s) (@lem3789471 A B _43482 f b s)). Qed.
Lemma lem3789481 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s) = (term22 A B _43482 f b s).
Proof. exact (TRANS (@lem3789467 A B f b s FINREC' _43482 h1) (@lem3789480 A B _43482 f b s)). Qed.
Lemma lem3789482 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789483 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s a) = (term26 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789481 A B f b s FINREC' _43482 h1) (@lem3789482 B a)). Qed.
Lemma lem3789485 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789486 {B : Type'} (f : type1424 B) (y : B) : (term27 B f y) = (f y).
Proof. exact (@lem3789485 B (nat -> Prop) f y). Qed.
Lemma lem3789487 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term28 A B _43482 f b s a) = (term26 A B _43482 f b s a).
Proof. exact (@lem3789486 B (term22 A B _43482 f b s) a). Qed.
Lemma lem3789488 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (_43480 : B) : (term26 A B _43482 f b s _43480) = (term29 A B _43482 f b s _43480).
Proof. exact (eq_refl (term26 A B _43482 f b s _43480)). Qed.
Lemma lem3789489 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term30 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (fun_ext (fun _43480 : B => @lem3789488 A B _43482 f b s _43480)). Qed.
Lemma lem3789490 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789491 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term28 A B _43482 f b s a) = (term26 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789489 A B _43482 f b s) (@lem3789490 B a)). Qed.
Lemma lem3789492 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem3789493 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term31 A B _43482 f b s a) = (term32 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789492) (@lem3789491 A B _43482 f b s a)). Qed.
Lemma lem3789494 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term26 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (eq_refl (term26 A B _43482 f b s a)). Qed.
Lemma lem3789495 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : ((term28 A B _43482 f b s a) = (term26 A B _43482 f b s a)) = ((term26 A B _43482 f b s a) = (term29 A B _43482 f b s a)).
Proof. exact (MK_COMB (@lem3789493 A B _43482 f b s a) (@lem3789494 A B _43482 f b s a)). Qed.
Lemma lem3789496 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term26 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (EQ_MP (@lem3789495 A B _43482 f b s a) (@lem3789487 A B _43482 f b s a)). Qed.
Lemma lem3789497 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s a) = (term29 A B _43482 f b s a).
Proof. exact (TRANS (@lem3789483 A B f b s a FINREC' _43482 h1) (@lem3789496 A B _43482 f b s a)). Qed.
Lemma lem3789498 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3789499 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term33 A B FINREC' f b s a) = (term34 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789497 A B f b s a FINREC' _43482 h1) (@lem3789498)). Qed.
Lemma lem3789501 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789502 (f : nat -> Prop) (y : nat) : (term35 f y) = (f y).
Proof. exact (@lem3789501 nat Prop f y). Qed.
Lemma lem3789503 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term36 A B _43482 f b s a) = (term34 A B _43482 f b s a).
Proof. exact (@lem3789502 (term29 A B _43482 f b s a) (NUMERAL 0)). Qed.
Lemma lem3789504 {A B : Type'} (_43482 : type1570 A B) (_43481 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term37 A B _43482 f b s a _43481) = (_43482 _43481 f b s a).
Proof. exact (eq_refl (term37 A B _43482 f b s a _43481)). Qed.
Lemma lem3789505 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term38 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (fun_ext (fun _43481 : nat => @lem3789504 A B _43482 _43481 f b s a)). Qed.
Lemma lem3789506 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3789507 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term36 A B _43482 f b s a) = (term34 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789505 A B _43482 f b s a) (@lem3789506)). Qed.
Lemma lem3789508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789509 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term39 A B _43482 f b s a) = (term40 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789508) (@lem3789507 A B _43482 f b s a)). Qed.
Lemma lem3789510 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term34 A B _43482 f b s a) = (term41 A B _43482 f b s a).
Proof. exact (eq_refl (term34 A B _43482 f b s a)). Qed.
Lemma lem3789511 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : ((term36 A B _43482 f b s a) = (term34 A B _43482 f b s a)) = ((term34 A B _43482 f b s a) = (term41 A B _43482 f b s a)).
Proof. exact (MK_COMB (@lem3789509 A B _43482 f b s a) (@lem3789510 A B _43482 f b s a)). Qed.
Lemma lem3789512 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term34 A B _43482 f b s a) = (term41 A B _43482 f b s a).
Proof. exact (EQ_MP (@lem3789511 A B _43482 f b s a) (@lem3789503 A B _43482 f b s a)). Qed.
Lemma lem3789513 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term33 A B FINREC' f b s a) = (term41 A B _43482 f b s a).
Proof. exact (TRANS (@lem3789499 A B f b s a FINREC' _43482 h1) (@lem3789512 A B _43482 f b s a)). Qed.
Lemma lem3789514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789515 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term42 A B FINREC' f b s a) = (term43 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789514) (@lem3789513 A B f b s a FINREC' _43482 h1)). Qed.
Lemma lem3789516 {A B : Type'} (s : A -> Prop) (a : B) (b : B) : (term44 A B s a b) = (term44 A B s a b).
Proof. exact (eq_refl (term44 A B s a b)). Qed.
Lemma lem3789517 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : ((term33 A B FINREC' f b s a) = (term44 A B s a b)) = ((term41 A B _43482 f b s a) = (term44 A B s a b)).
Proof. exact (MK_COMB (@lem3789515 A B f b s a FINREC' _43482 h1) (@lem3789516 A B s a b)). Qed.
Lemma lem3789518 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term45 A B FINREC' f s a) = (term46 A B _43482 f s a).
Proof. exact (fun_ext (fun b : B => @lem3789517 A B f s a b FINREC' _43482 h1)). Qed.
Lemma lem3789519 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3789520 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term47 A B FINREC' f s a) = (term48 A B _43482 f s a).
Proof. exact (MK_COMB (@lem3789519 B) (@lem3789518 A B f s a FINREC' _43482 h1)). Qed.
Lemma lem3789521 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term49 A B FINREC' f s) = (term50 A B _43482 f s).
Proof. exact (fun_ext (fun a : B => @lem3789520 A B f s a FINREC' _43482 h1)). Qed.
Lemma lem3789522 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3789523 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term51 A B FINREC' f s) = (term52 A B _43482 f s).
Proof. exact (MK_COMB (@lem3789522 B) (@lem3789521 A B f s FINREC' _43482 h1)). Qed.
Lemma lem3789524 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term53 A B FINREC' f) = (term54 A B _43482 f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3789523 A B f s FINREC' _43482 h1)). Qed.
Lemma lem3789525 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3789526 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term55 A B FINREC' f) = (term56 A B _43482 f).
Proof. exact (MK_COMB (@lem3789525 A) (@lem3789524 A B f FINREC' _43482 h1)). Qed.
Lemma lem3789527 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term57 A B FINREC') = (term58 A B _43482).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3789526 A B f FINREC' _43482 h1)). Qed.
Lemma lem3789528 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3789529 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term59 A B FINREC') = (term60 A B _43482).
Proof. exact (MK_COMB (@lem3789528 A B) (@lem3789527 A B FINREC' _43482 h1)). Qed.
Lemma lem3789530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3789531 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term61 A B FINREC') = (term62 A B _43482).
Proof. exact (MK_COMB (@lem3789530) (@lem3789529 A B FINREC' _43482 h1)). Qed.
Lemma lem3789533 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : FINREC' = (term4 A B _43482).
Proof. exact (h1). Qed.
Lemma lem3789534 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789535 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789533 A B FINREC' _43482 h1) (@lem3789534 A B f)). Qed.
Lemma lem3789537 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789538 {A B : Type'} (f : type431 A B) (y : type1411 A B) : (term6 A B f y) = (f y).
Proof. exact (@lem3789537 (type1411 A B) (type1449 A B) f y). Qed.
Lemma lem3789539 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (@lem3789538 A B (term4 A B _43482) f). Qed.
Lemma lem3789540 {A B : Type'} (_43482 : type1570 A B) (_43477 : type1411 A B) : (term5 A B _43482 _43477) = (term8 A B _43482 _43477).
Proof. exact (eq_refl (term5 A B _43482 _43477)). Qed.
Lemma lem3789541 {A B : Type'} (_43482 : type1570 A B) : (term9 A B _43482) = (term4 A B _43482).
Proof. exact (fun_ext (fun _43477 : type1411 A B => @lem3789540 A B _43482 _43477)). Qed.
Lemma lem3789542 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789543 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789541 A B _43482) (@lem3789542 A B f)). Qed.
Lemma lem3789544 {A B : Type'} : (@eq (B -> (A -> Prop) -> B -> nat -> Prop)) = (@eq (B -> (A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> (A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789545 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term10 A B _43482 f) = (term11 A B _43482 f).
Proof. exact (MK_COMB (@lem3789544 A B) (@lem3789543 A B _43482 f)). Qed.
Lemma lem3789546 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (eq_refl (term5 A B _43482 f)). Qed.
Lemma lem3789547 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : ((term7 A B _43482 f) = (term5 A B _43482 f)) = ((term5 A B _43482 f) = (term8 A B _43482 f)).
Proof. exact (MK_COMB (@lem3789545 A B _43482 f) (@lem3789546 A B _43482 f)). Qed.
Lemma lem3789548 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (EQ_MP (@lem3789547 A B _43482 f) (@lem3789539 A B _43482 f)). Qed.
Lemma lem3789549 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term8 A B _43482 f).
Proof. exact (TRANS (@lem3789535 A B f FINREC' _43482 h1) (@lem3789548 A B _43482 f)). Qed.
Lemma lem3789550 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789551 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789549 A B f FINREC' _43482 h1) (@lem3789550 B b)). Qed.
Lemma lem3789553 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789554 {A B : Type'} (f : type1449 A B) (y : B) : (term13 A B f y) = (f y).
Proof. exact (@lem3789553 B (type676 A B) f y). Qed.
Lemma lem3789555 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (@lem3789554 A B (term8 A B _43482 f) b). Qed.
Lemma lem3789556 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (_43478 : B) : (term12 A B _43482 f _43478) = (term15 A B _43482 f _43478).
Proof. exact (eq_refl (term12 A B _43482 f _43478)). Qed.
Lemma lem3789557 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term16 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (fun_ext (fun _43478 : B => @lem3789556 A B _43482 f _43478)). Qed.
Lemma lem3789558 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789559 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789557 A B _43482 f) (@lem3789558 B b)). Qed.
Lemma lem3789560 {A B : Type'} : (@eq ((A -> Prop) -> B -> nat -> Prop)) = (@eq ((A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789561 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term17 A B _43482 f b) = (term18 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789560 A B) (@lem3789559 A B _43482 f b)). Qed.
Lemma lem3789562 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (eq_refl (term12 A B _43482 f b)). Qed.
Lemma lem3789563 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : ((term14 A B _43482 f b) = (term12 A B _43482 f b)) = ((term12 A B _43482 f b) = (term15 A B _43482 f b)).
Proof. exact (MK_COMB (@lem3789561 A B _43482 f b) (@lem3789562 A B _43482 f b)). Qed.
Lemma lem3789564 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (EQ_MP (@lem3789563 A B _43482 f b) (@lem3789555 A B _43482 f b)). Qed.
Lemma lem3789565 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term15 A B _43482 f b).
Proof. exact (TRANS (@lem3789551 A B f b FINREC' _43482 h1) (@lem3789564 A B _43482 f b)). Qed.
Lemma lem3789566 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789567 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s) = (term19 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789565 A B f b FINREC' _43482 h1) (@lem3789566 A s)). Qed.
Lemma lem3789569 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789570 {A B : Type'} (f : type676 A B) (y : A -> Prop) : (term20 A B f y) = (f y).
Proof. exact (@lem3789569 (A -> Prop) (type1424 B) f y). Qed.
Lemma lem3789571 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term21 A B _43482 f b s) = (term19 A B _43482 f b s).
Proof. exact (@lem3789570 A B (term15 A B _43482 f b) s). Qed.
Lemma lem3789572 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (_43479 : A -> Prop) : (term19 A B _43482 f b _43479) = (term22 A B _43482 f b _43479).
Proof. exact (eq_refl (term19 A B _43482 f b _43479)). Qed.
Lemma lem3789573 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term23 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (fun_ext (fun _43479 : A -> Prop => @lem3789572 A B _43482 f b _43479)). Qed.
Lemma lem3789574 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789575 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term21 A B _43482 f b s) = (term19 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789573 A B _43482 f b) (@lem3789574 A s)). Qed.
Lemma lem3789576 {B : Type'} : (@eq (B -> nat -> Prop)) = (@eq (B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> nat -> Prop))). Qed.
Lemma lem3789577 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term24 A B _43482 f b s) = (term25 A B _43482 f b s).
Proof. exact (MK_COMB (@lem3789576 B) (@lem3789575 A B _43482 f b s)). Qed.
Lemma lem3789578 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term19 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (eq_refl (term19 A B _43482 f b s)). Qed.
Lemma lem3789579 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : ((term21 A B _43482 f b s) = (term19 A B _43482 f b s)) = ((term19 A B _43482 f b s) = (term22 A B _43482 f b s)).
Proof. exact (MK_COMB (@lem3789577 A B _43482 f b s) (@lem3789578 A B _43482 f b s)). Qed.
Lemma lem3789580 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term19 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (EQ_MP (@lem3789579 A B _43482 f b s) (@lem3789571 A B _43482 f b s)). Qed.
Lemma lem3789581 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s) = (term22 A B _43482 f b s).
Proof. exact (TRANS (@lem3789567 A B f b s FINREC' _43482 h1) (@lem3789580 A B _43482 f b s)). Qed.
Lemma lem3789582 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789583 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s a) = (term26 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789581 A B f b s FINREC' _43482 h1) (@lem3789582 B a)). Qed.
Lemma lem3789585 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789586 {B : Type'} (f : type1424 B) (y : B) : (term27 B f y) = (f y).
Proof. exact (@lem3789585 B (nat -> Prop) f y). Qed.
Lemma lem3789587 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term28 A B _43482 f b s a) = (term26 A B _43482 f b s a).
Proof. exact (@lem3789586 B (term22 A B _43482 f b s) a). Qed.
Lemma lem3789588 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (_43480 : B) : (term26 A B _43482 f b s _43480) = (term29 A B _43482 f b s _43480).
Proof. exact (eq_refl (term26 A B _43482 f b s _43480)). Qed.
Lemma lem3789589 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term30 A B _43482 f b s) = (term22 A B _43482 f b s).
Proof. exact (fun_ext (fun _43480 : B => @lem3789588 A B _43482 f b s _43480)). Qed.
Lemma lem3789590 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789591 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term28 A B _43482 f b s a) = (term26 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789589 A B _43482 f b s) (@lem3789590 B a)). Qed.
Lemma lem3789592 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem3789593 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term31 A B _43482 f b s a) = (term32 A B _43482 f b s a).
Proof. exact (MK_COMB (@lem3789592) (@lem3789591 A B _43482 f b s a)). Qed.
Lemma lem3789594 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term26 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (eq_refl (term26 A B _43482 f b s a)). Qed.
Lemma lem3789595 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : ((term28 A B _43482 f b s a) = (term26 A B _43482 f b s a)) = ((term26 A B _43482 f b s a) = (term29 A B _43482 f b s a)).
Proof. exact (MK_COMB (@lem3789593 A B _43482 f b s a) (@lem3789594 A B _43482 f b s a)). Qed.
Lemma lem3789596 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term26 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (EQ_MP (@lem3789595 A B _43482 f b s a) (@lem3789587 A B _43482 f b s a)). Qed.
Lemma lem3789597 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b s a) = (term29 A B _43482 f b s a).
Proof. exact (TRANS (@lem3789583 A B f b s a FINREC' _43482 h1) (@lem3789596 A B _43482 f b s a)). Qed.
Lemma lem3789598 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3789599 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term63 A B FINREC' f b s a n) = (term64 A B _43482 f b s a n).
Proof. exact (MK_COMB (@lem3789597 A B f b s a FINREC' _43482 h1) (@lem3789598 n)). Qed.
Lemma lem3789601 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789602 (f : nat -> Prop) (y : nat) : (term35 f y) = (f y).
Proof. exact (@lem3789601 nat Prop f y). Qed.
Lemma lem3789603 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term65 A B _43482 f b s a n) = (term64 A B _43482 f b s a n).
Proof. exact (@lem3789602 (term29 A B _43482 f b s a) (S n)). Qed.
Lemma lem3789604 {A B : Type'} (_43482 : type1570 A B) (_43481 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term37 A B _43482 f b s a _43481) = (_43482 _43481 f b s a).
Proof. exact (eq_refl (term37 A B _43482 f b s a _43481)). Qed.
Lemma lem3789605 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term38 A B _43482 f b s a) = (term29 A B _43482 f b s a).
Proof. exact (fun_ext (fun _43481 : nat => @lem3789604 A B _43482 _43481 f b s a)). Qed.
Lemma lem3789606 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3789607 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term65 A B _43482 f b s a n) = (term64 A B _43482 f b s a n).
Proof. exact (MK_COMB (@lem3789605 A B _43482 f b s a) (@lem3789606 n)). Qed.
Lemma lem3789608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789609 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term66 A B _43482 f b s a n) = (term67 A B _43482 f b s a n).
Proof. exact (MK_COMB (@lem3789608) (@lem3789607 A B _43482 f b s a n)). Qed.
Lemma lem3789610 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term64 A B _43482 f b s a n) = (term68 A B _43482 n f b s a).
Proof. exact (eq_refl (term64 A B _43482 f b s a n)). Qed.
Lemma lem3789611 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : ((term65 A B _43482 f b s a n) = (term64 A B _43482 f b s a n)) = ((term64 A B _43482 f b s a n) = (term68 A B _43482 n f b s a)).
Proof. exact (MK_COMB (@lem3789609 A B _43482 f b s a n) (@lem3789610 A B _43482 n f b s a)). Qed.
Lemma lem3789612 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term64 A B _43482 f b s a n) = (term68 A B _43482 n f b s a).
Proof. exact (EQ_MP (@lem3789611 A B _43482 n f b s a) (@lem3789603 A B _43482 f b s a n)). Qed.
Lemma lem3789613 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term63 A B FINREC' f b s a n) = (term68 A B _43482 n f b s a).
Proof. exact (TRANS (@lem3789599 A B f b s a n FINREC' _43482 h1) (@lem3789612 A B _43482 n f b s a)). Qed.
Lemma lem3789614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789615 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term69 A B FINREC' f b s a n) = (term70 A B _43482 n f b s a).
Proof. exact (MK_COMB (@lem3789614) (@lem3789613 A B n f b s a FINREC' _43482 h1)). Qed.
Lemma lem3789617 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : FINREC' = (term4 A B _43482).
Proof. exact (h1). Qed.
Lemma lem3789618 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789619 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789617 A B FINREC' _43482 h1) (@lem3789618 A B f)). Qed.
Lemma lem3789621 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789622 {A B : Type'} (f : type431 A B) (y : type1411 A B) : (term6 A B f y) = (f y).
Proof. exact (@lem3789621 (type1411 A B) (type1449 A B) f y). Qed.
Lemma lem3789623 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (@lem3789622 A B (term4 A B _43482) f). Qed.
Lemma lem3789624 {A B : Type'} (_43482 : type1570 A B) (_43477 : type1411 A B) : (term5 A B _43482 _43477) = (term8 A B _43482 _43477).
Proof. exact (eq_refl (term5 A B _43482 _43477)). Qed.
Lemma lem3789625 {A B : Type'} (_43482 : type1570 A B) : (term9 A B _43482) = (term4 A B _43482).
Proof. exact (fun_ext (fun _43477 : type1411 A B => @lem3789624 A B _43482 _43477)). Qed.
Lemma lem3789626 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789627 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term7 A B _43482 f) = (term5 A B _43482 f).
Proof. exact (MK_COMB (@lem3789625 A B _43482) (@lem3789626 A B f)). Qed.
Lemma lem3789628 {A B : Type'} : (@eq (B -> (A -> Prop) -> B -> nat -> Prop)) = (@eq (B -> (A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> (A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789629 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term10 A B _43482 f) = (term11 A B _43482 f).
Proof. exact (MK_COMB (@lem3789628 A B) (@lem3789627 A B _43482 f)). Qed.
Lemma lem3789630 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (eq_refl (term5 A B _43482 f)). Qed.
Lemma lem3789631 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : ((term7 A B _43482 f) = (term5 A B _43482 f)) = ((term5 A B _43482 f) = (term8 A B _43482 f)).
Proof. exact (MK_COMB (@lem3789629 A B _43482 f) (@lem3789630 A B _43482 f)). Qed.
Lemma lem3789632 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term5 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (EQ_MP (@lem3789631 A B _43482 f) (@lem3789623 A B _43482 f)). Qed.
Lemma lem3789633 {A B : Type'} (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f) = (term8 A B _43482 f).
Proof. exact (TRANS (@lem3789619 A B f FINREC' _43482 h1) (@lem3789632 A B _43482 f)). Qed.
Lemma lem3789634 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789635 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789633 A B f FINREC' _43482 h1) (@lem3789634 B b)). Qed.
Lemma lem3789637 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789638 {A B : Type'} (f : type1449 A B) (y : B) : (term13 A B f y) = (f y).
Proof. exact (@lem3789637 B (type676 A B) f y). Qed.
Lemma lem3789639 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (@lem3789638 A B (term8 A B _43482 f) b). Qed.
Lemma lem3789640 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (_43478 : B) : (term12 A B _43482 f _43478) = (term15 A B _43482 f _43478).
Proof. exact (eq_refl (term12 A B _43482 f _43478)). Qed.
Lemma lem3789641 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term16 A B _43482 f) = (term8 A B _43482 f).
Proof. exact (fun_ext (fun _43478 : B => @lem3789640 A B _43482 f _43478)). Qed.
Lemma lem3789642 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789643 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term14 A B _43482 f b) = (term12 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789641 A B _43482 f) (@lem3789642 B b)). Qed.
Lemma lem3789644 {A B : Type'} : (@eq ((A -> Prop) -> B -> nat -> Prop)) = (@eq ((A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789645 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term17 A B _43482 f b) = (term18 A B _43482 f b).
Proof. exact (MK_COMB (@lem3789644 A B) (@lem3789643 A B _43482 f b)). Qed.
Lemma lem3789646 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (eq_refl (term12 A B _43482 f b)). Qed.
Lemma lem3789647 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : ((term14 A B _43482 f b) = (term12 A B _43482 f b)) = ((term12 A B _43482 f b) = (term15 A B _43482 f b)).
Proof. exact (MK_COMB (@lem3789645 A B _43482 f b) (@lem3789646 A B _43482 f b)). Qed.
Lemma lem3789648 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term12 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (EQ_MP (@lem3789647 A B _43482 f b) (@lem3789639 A B _43482 f b)). Qed.
Lemma lem3789649 {A B : Type'} (f : type1411 A B) (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (FINREC' f b) = (term15 A B _43482 f b).
Proof. exact (TRANS (@lem3789635 A B f b FINREC' _43482 h1) (@lem3789648 A B _43482 f b)). Qed.
Lemma lem3789650 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@DELETE A s x).
Proof. exact (eq_refl (@DELETE A s x)). Qed.
Lemma lem3789651 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term71 A B FINREC' f b s x) = (term72 A B _43482 f b s x).
Proof. exact (MK_COMB (@lem3789649 A B f b FINREC' _43482 h1) (@lem3789650 A s x)). Qed.
Lemma lem3789653 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789654 {A B : Type'} (f : type676 A B) (y : A -> Prop) : (term20 A B f y) = (f y).
Proof. exact (@lem3789653 (A -> Prop) (type1424 B) f y). Qed.
Lemma lem3789655 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term73 A B _43482 f b s x) = (term72 A B _43482 f b s x).
Proof. exact (@lem3789654 A B (term15 A B _43482 f b) (@DELETE A s x)). Qed.
Lemma lem3789656 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (_43479 : A -> Prop) : (term19 A B _43482 f b _43479) = (term22 A B _43482 f b _43479).
Proof. exact (eq_refl (term19 A B _43482 f b _43479)). Qed.
Lemma lem3789657 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term23 A B _43482 f b) = (term15 A B _43482 f b).
Proof. exact (fun_ext (fun _43479 : A -> Prop => @lem3789656 A B _43482 f b _43479)). Qed.
Lemma lem3789658 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@DELETE A s x).
Proof. exact (eq_refl (@DELETE A s x)). Qed.
Lemma lem3789659 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term73 A B _43482 f b s x) = (term72 A B _43482 f b s x).
Proof. exact (MK_COMB (@lem3789657 A B _43482 f b) (@lem3789658 A s x)). Qed.
Lemma lem3789660 {B : Type'} : (@eq (B -> nat -> Prop)) = (@eq (B -> nat -> Prop)).
Proof. exact (eq_refl (@eq (B -> nat -> Prop))). Qed.
Lemma lem3789661 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term74 A B _43482 f b s x) = (term75 A B _43482 f b s x).
Proof. exact (MK_COMB (@lem3789660 B) (@lem3789659 A B _43482 f b s x)). Qed.
Lemma lem3789662 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term72 A B _43482 f b s x) = (term76 A B _43482 f b s x).
Proof. exact (eq_refl (term72 A B _43482 f b s x)). Qed.
Lemma lem3789663 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : ((term73 A B _43482 f b s x) = (term72 A B _43482 f b s x)) = ((term72 A B _43482 f b s x) = (term76 A B _43482 f b s x)).
Proof. exact (MK_COMB (@lem3789661 A B _43482 f b s x) (@lem3789662 A B _43482 f b s x)). Qed.
Lemma lem3789664 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term72 A B _43482 f b s x) = (term76 A B _43482 f b s x).
Proof. exact (EQ_MP (@lem3789663 A B _43482 f b s x) (@lem3789655 A B _43482 f b s x)). Qed.
Lemma lem3789665 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term71 A B FINREC' f b s x) = (term76 A B _43482 f b s x).
Proof. exact (TRANS (@lem3789651 A B f b s x FINREC' _43482 h1) (@lem3789664 A B _43482 f b s x)). Qed.
Lemma lem3789666 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3789667 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term77 A B FINREC' f b s x c) = (term78 A B _43482 f b s x c).
Proof. exact (MK_COMB (@lem3789665 A B f b s x FINREC' _43482 h1) (@lem3789666 B c)). Qed.
Lemma lem3789669 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789670 {B : Type'} (f : type1424 B) (y : B) : (term27 B f y) = (f y).
Proof. exact (@lem3789669 B (nat -> Prop) f y). Qed.
Lemma lem3789671 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term79 A B _43482 f b s x c) = (term78 A B _43482 f b s x c).
Proof. exact (@lem3789670 B (term76 A B _43482 f b s x) c). Qed.
Lemma lem3789672 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (_43480 : B) : (term78 A B _43482 f b s x _43480) = (term80 A B _43482 f b s x _43480).
Proof. exact (eq_refl (term78 A B _43482 f b s x _43480)). Qed.
Lemma lem3789673 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term81 A B _43482 f b s x) = (term76 A B _43482 f b s x).
Proof. exact (fun_ext (fun _43480 : B => @lem3789672 A B _43482 f b s x _43480)). Qed.
Lemma lem3789674 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3789675 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term79 A B _43482 f b s x c) = (term78 A B _43482 f b s x c).
Proof. exact (MK_COMB (@lem3789673 A B _43482 f b s x) (@lem3789674 B c)). Qed.
Lemma lem3789676 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem3789677 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term82 A B _43482 f b s x c) = (term83 A B _43482 f b s x c).
Proof. exact (MK_COMB (@lem3789676) (@lem3789675 A B _43482 f b s x c)). Qed.
Lemma lem3789678 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term78 A B _43482 f b s x c) = (term80 A B _43482 f b s x c).
Proof. exact (eq_refl (term78 A B _43482 f b s x c)). Qed.
Lemma lem3789679 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : ((term79 A B _43482 f b s x c) = (term78 A B _43482 f b s x c)) = ((term78 A B _43482 f b s x c) = (term80 A B _43482 f b s x c)).
Proof. exact (MK_COMB (@lem3789677 A B _43482 f b s x c) (@lem3789678 A B _43482 f b s x c)). Qed.
Lemma lem3789680 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term78 A B _43482 f b s x c) = (term80 A B _43482 f b s x c).
Proof. exact (EQ_MP (@lem3789679 A B _43482 f b s x c) (@lem3789671 A B _43482 f b s x c)). Qed.
Lemma lem3789681 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term77 A B FINREC' f b s x c) = (term80 A B _43482 f b s x c).
Proof. exact (TRANS (@lem3789667 A B f b s x c FINREC' _43482 h1) (@lem3789680 A B _43482 f b s x c)). Qed.
Lemma lem3789682 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3789683 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term84 A B FINREC' f b s x c n) = (term85 A B _43482 f b s x c n).
Proof. exact (MK_COMB (@lem3789681 A B f b s x c FINREC' _43482 h1) (@lem3789682 n)). Qed.
Lemma lem3789685 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem3789430 A B f y) (@lem3789429 A B f y)). Qed.
Lemma lem3789686 (f : nat -> Prop) (y : nat) : (term35 f y) = (f y).
Proof. exact (@lem3789685 nat Prop f y). Qed.
Lemma lem3789687 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) : (term86 A B _43482 f b s x c n) = (term85 A B _43482 f b s x c n).
Proof. exact (@lem3789686 (term80 A B _43482 f b s x c) n). Qed.
Lemma lem3789688 {A B : Type'} (_43482 : type1570 A B) (_43481 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term85 A B _43482 f b s x c _43481) = (term87 A B _43482 _43481 f b s x c).
Proof. exact (eq_refl (term85 A B _43482 f b s x c _43481)). Qed.
Lemma lem3789689 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term88 A B _43482 f b s x c) = (term80 A B _43482 f b s x c).
Proof. exact (fun_ext (fun _43481 : nat => @lem3789688 A B _43482 _43481 f b s x c)). Qed.
Lemma lem3789690 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3789691 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) : (term86 A B _43482 f b s x c n) = (term85 A B _43482 f b s x c n).
Proof. exact (MK_COMB (@lem3789689 A B _43482 f b s x c) (@lem3789690 n)). Qed.
Lemma lem3789692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789693 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) : (term89 A B _43482 f b s x c n) = (term90 A B _43482 f b s x c n).
Proof. exact (MK_COMB (@lem3789692) (@lem3789691 A B _43482 f b s x c n)). Qed.
Lemma lem3789694 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term85 A B _43482 f b s x c n) = (term87 A B _43482 n f b s x c).
Proof. exact (eq_refl (term85 A B _43482 f b s x c n)). Qed.
Lemma lem3789695 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : ((term86 A B _43482 f b s x c n) = (term85 A B _43482 f b s x c n)) = ((term85 A B _43482 f b s x c n) = (term87 A B _43482 n f b s x c)).
Proof. exact (MK_COMB (@lem3789693 A B _43482 f b s x c n) (@lem3789694 A B _43482 n f b s x c)). Qed.
Lemma lem3789696 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term85 A B _43482 f b s x c n) = (term87 A B _43482 n f b s x c).
Proof. exact (EQ_MP (@lem3789695 A B _43482 n f b s x c) (@lem3789687 A B _43482 f b s x c n)). Qed.
Lemma lem3789697 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term84 A B FINREC' f b s x c n) = (term87 A B _43482 n f b s x c).
Proof. exact (TRANS (@lem3789683 A B f b s x c n FINREC' _43482 h1) (@lem3789696 A B _43482 n f b s x c)). Qed.
Lemma lem3789698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3789699 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term91 A B FINREC' f b s x c n) = (term92 A B _43482 n f b s x c).
Proof. exact (MK_COMB (@lem3789698) (@lem3789697 A B n f b s x c FINREC' _43482 h1)). Qed.
Lemma lem3789700 {A B : Type'} (a : B) (f : type1411 A B) (x : A) (c : B) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3789701 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term93 A B FINREC' b s n a f x c) = (term94 A B _43482 n b s a f x c).
Proof. exact (MK_COMB (@lem3789699 A B n f b s x c FINREC' _43482 h1) (@lem3789700 A B a f x c)). Qed.
Lemma lem3789702 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (eq_refl (term95 A x s)). Qed.
Lemma lem3789703 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (x : A) (c : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term96 A B FINREC' b s n a f x c) = (term97 A B _43482 n b s a f x c).
Proof. exact (MK_COMB (@lem3789702 A x s) (@lem3789701 A B n b s a f x c FINREC' _43482 h1)). Qed.
Lemma lem3789704 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (x : A) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term98 A B FINREC' b s n a f x) = (term99 A B _43482 n b s a f x).
Proof. exact (fun_ext (fun c : B => @lem3789703 A B n b s a f x c FINREC' _43482 h1)). Qed.
Lemma lem3789705 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3789706 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (x : A) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term100 A B FINREC' b s n a f x) = (term101 A B _43482 n b s a f x).
Proof. exact (MK_COMB (@lem3789705 B) (@lem3789704 A B n b s a f x FINREC' _43482 h1)). Qed.
Lemma lem3789707 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term102 A B FINREC' b s n a f) = (term103 A B _43482 n b s a f).
Proof. exact (fun_ext (fun x : A => @lem3789706 A B n b s a f x FINREC' _43482 h1)). Qed.
Lemma lem3789708 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3789709 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term104 A B FINREC' b s n a f) = (term105 A B _43482 n b s a f).
Proof. exact (MK_COMB (@lem3789708 A) (@lem3789707 A B n b s a f FINREC' _43482 h1)). Qed.
Lemma lem3789710 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : ((term63 A B FINREC' f b s a n) = (term104 A B FINREC' b s n a f)) = ((term68 A B _43482 n f b s a) = (term105 A B _43482 n b s a f)).
Proof. exact (MK_COMB (@lem3789615 A B n f b s a FINREC' _43482 h1) (@lem3789709 A B n b s a f FINREC' _43482 h1)). Qed.
Lemma lem3789711 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term106 A B FINREC' b s n a) = (term107 A B _43482 n b s a).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3789710 A B n b s a f FINREC' _43482 h1)). Qed.
Lemma lem3789712 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3789713 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term108 A B FINREC' b s n a) = (term109 A B _43482 n b s a).
Proof. exact (MK_COMB (@lem3789712 A B) (@lem3789711 A B n b s a FINREC' _43482 h1)). Qed.
Lemma lem3789714 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term110 A B FINREC' b s n) = (term111 A B _43482 n b s).
Proof. exact (fun_ext (fun a : B => @lem3789713 A B n b s a FINREC' _43482 h1)). Qed.
Lemma lem3789715 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3789716 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term112 A B FINREC' b s n) = (term113 A B _43482 n b s).
Proof. exact (MK_COMB (@lem3789715 B) (@lem3789714 A B n b s FINREC' _43482 h1)). Qed.
Lemma lem3789717 {A B : Type'} (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term114 A B FINREC' b s) = (term115 A B _43482 b s).
Proof. exact (fun_ext (fun n : nat => @lem3789716 A B n b s FINREC' _43482 h1)). Qed.
Lemma lem3789718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3789719 {A B : Type'} (b : B) (s : A -> Prop) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term116 A B FINREC' b s) = (term117 A B _43482 b s).
Proof. exact (MK_COMB (@lem3789718) (@lem3789717 A B b s FINREC' _43482 h1)). Qed.
Lemma lem3789720 {A B : Type'} (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term118 A B FINREC' b) = (term119 A B _43482 b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3789719 A B b s FINREC' _43482 h1)). Qed.
Lemma lem3789721 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3789722 {A B : Type'} (b : B) (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term120 A B FINREC' b) = (term121 A B _43482 b).
Proof. exact (MK_COMB (@lem3789721 A) (@lem3789720 A B b FINREC' _43482 h1)). Qed.
Lemma lem3789723 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term122 A B FINREC') = (term123 A B _43482).
Proof. exact (fun_ext (fun b : B => @lem3789722 A B b FINREC' _43482 h1)). Qed.
Lemma lem3789724 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3789725 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term124 A B FINREC') = (term125 A B _43482).
Proof. exact (MK_COMB (@lem3789724 B) (@lem3789723 A B FINREC' _43482 h1)). Qed.
Lemma lem3789726 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term126 A B FINREC') = (term127 A B _43482).
Proof. exact (MK_COMB (@lem3789531 A B FINREC' _43482 h1) (@lem3789725 A B FINREC' _43482 h1)). Qed.
Lemma lem3789727 {A B : Type'} (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term128 A B _43482) = (term129 A B).
Proof. exact (h1). Qed.
Lemma lem3789728 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789729 {A B : Type'} (f : type1411 A B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term130 A B _43482 f) = (term131 A B f).
Proof. exact (MK_COMB (@lem3789727 A B _43482 h1) (@lem3789728 A B f)). Qed.
Lemma lem3789730 {A B : Type'} (f : type1411 A B) : (term131 A B f) = (term132 A B).
Proof. exact (eq_refl (term131 A B f)). Qed.
Lemma lem3789731 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : (term133 A B _43482 f) = (term133 A B _43482 f).
Proof. exact (eq_refl (term133 A B _43482 f)). Qed.
Lemma lem3789732 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) : ((term130 A B _43482 f) = (term131 A B f)) = ((term130 A B _43482 f) = (term132 A B)).
Proof. exact (MK_COMB (@lem3789731 A B _43482 f) (@lem3789730 A B f)). Qed.
Lemma lem3789733 {A B : Type'} (f : type1411 A B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term130 A B _43482 f) = (term132 A B).
Proof. exact (EQ_MP (@lem3789732 A B _43482 f) (@lem3789729 A B f _43482 h1)). Qed.
Lemma lem3789734 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789735 {A B : Type'} (f : type1411 A B) (b : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term134 A B _43482 f b) = (term135 A B b).
Proof. exact (MK_COMB (@lem3789733 A B f _43482 h1) (@lem3789734 B b)). Qed.
Lemma lem3789736 {A B : Type'} (b : B) : (term135 A B b) = (term136 A B b).
Proof. exact (eq_refl (term135 A B b)). Qed.
Lemma lem3789737 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : (term137 A B _43482 f b) = (term137 A B _43482 f b).
Proof. exact (eq_refl (term137 A B _43482 f b)). Qed.
Lemma lem3789738 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) : ((term134 A B _43482 f b) = (term135 A B b)) = ((term134 A B _43482 f b) = (term136 A B b)).
Proof. exact (MK_COMB (@lem3789737 A B _43482 f b) (@lem3789736 A B b)). Qed.
Lemma lem3789739 {A B : Type'} (f : type1411 A B) (b : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term134 A B _43482 f b) = (term136 A B b).
Proof. exact (EQ_MP (@lem3789738 A B _43482 f b) (@lem3789735 A B f b _43482 h1)). Qed.
Lemma lem3789740 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789741 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term138 A B _43482 f b s) = (term139 A B b s).
Proof. exact (MK_COMB (@lem3789739 A B f b _43482 h1) (@lem3789740 A s)). Qed.
Lemma lem3789742 {A B : Type'} (s : A -> Prop) (b : B) : (term139 A B b s) = (term140 A B s b).
Proof. exact (eq_refl (term139 A B b s)). Qed.
Lemma lem3789743 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) : (term141 A B _43482 f b s) = (term141 A B _43482 f b s).
Proof. exact (eq_refl (term141 A B _43482 f b s)). Qed.
Lemma lem3789744 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (s : A -> Prop) (b : B) : ((term138 A B _43482 f b s) = (term139 A B b s)) = ((term138 A B _43482 f b s) = (term140 A B s b)).
Proof. exact (MK_COMB (@lem3789743 A B _43482 f b s) (@lem3789742 A B s b)). Qed.
Lemma lem3789745 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term138 A B _43482 f b s) = (term140 A B s b).
Proof. exact (EQ_MP (@lem3789744 A B _43482 f s b) (@lem3789741 A B f b s _43482 h1)). Qed.
Lemma lem3789746 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789747 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term41 A B _43482 f b s a) = (term142 A B s b a).
Proof. exact (MK_COMB (@lem3789745 A B f s b _43482 h1) (@lem3789746 B a)). Qed.
Lemma lem3789748 {A B : Type'} (s : A -> Prop) (a : B) (b : B) : (term142 A B s b a) = (term44 A B s a b).
Proof. exact (eq_refl (term142 A B s b a)). Qed.
Lemma lem3789749 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term43 A B _43482 f b s a) = (term43 A B _43482 f b s a).
Proof. exact (eq_refl (term43 A B _43482 f b s a)). Qed.
Lemma lem3789750 {A B : Type'} (_43482 : type1570 A B) (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : ((term41 A B _43482 f b s a) = (term142 A B s b a)) = ((term41 A B _43482 f b s a) = (term44 A B s a b)).
Proof. exact (MK_COMB (@lem3789749 A B _43482 f b s a) (@lem3789748 A B s a b)). Qed.
Lemma lem3789751 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : (term41 A B _43482 f b s a) = (term44 A B s a b).
Proof. exact (EQ_MP (@lem3789750 A B _43482 f s a b) (@lem3789747 A B f s b a _43482 h1)). Qed.
Lemma lem3789752 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : term48 A B _43482 f s a.
Proof. exact (fun b : B => @lem3789751 A B f s a b _43482 h1). Qed.
Lemma lem3789753 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : term52 A B _43482 f s.
Proof. exact (fun a : B => @lem3789752 A B f s a _43482 h1). Qed.
Lemma lem3789754 {A B : Type'} (f : type1411 A B) (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : term56 A B _43482 f.
Proof. exact (fun s : A -> Prop => @lem3789753 A B f s _43482 h1). Qed.
Lemma lem3789755 {A B : Type'} (_43482 : type1570 A B) (h1 : (term128 A B _43482) = (term129 A B)) : term60 A B _43482.
Proof. exact (fun f : type1411 A B => @lem3789754 A B f _43482 h1). Qed.
Lemma lem3789756 {A B : Type'} (_43482 : type1570 A B) (h1 : term143 A B _43482) : term143 A B _43482.
Proof. exact (h1). Qed.
Lemma lem3789757 {A B : Type'} (n : nat) (_43482 : type1570 A B) (h1 : term143 A B _43482) : term144 A B _43482 n.
Proof. exact (@lem3789756 A B _43482 h1 n). Qed.
Lemma lem3789758 {A B : Type'} (_43482 : type1570 A B) (n : nat) : (term144 A B _43482 n) = ((term145 A B _43482 n) = (term146 A B _43482 n)).
Proof. exact (eq_refl (term144 A B _43482 n)). Qed.
Lemma lem3789759 {A B : Type'} (n : nat) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term145 A B _43482 n) = (term146 A B _43482 n).
Proof. exact (EQ_MP (@lem3789758 A B _43482 n) (@lem3789757 A B n _43482 h1)). Qed.
Lemma lem3789760 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3789761 {A B : Type'} (n : nat) (f : type1411 A B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term147 A B _43482 n f) = (term148 A B _43482 n f).
Proof. exact (MK_COMB (@lem3789759 A B n _43482 h1) (@lem3789760 A B f)). Qed.
Lemma lem3789762 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) : (term148 A B _43482 n f) = (term149 A B _43482 n f).
Proof. exact (eq_refl (term148 A B _43482 n f)). Qed.
Lemma lem3789763 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) : (term150 A B _43482 n f) = (term150 A B _43482 n f).
Proof. exact (eq_refl (term150 A B _43482 n f)). Qed.
Lemma lem3789764 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) : ((term147 A B _43482 n f) = (term148 A B _43482 n f)) = ((term147 A B _43482 n f) = (term149 A B _43482 n f)).
Proof. exact (MK_COMB (@lem3789763 A B _43482 n f) (@lem3789762 A B _43482 n f)). Qed.
Lemma lem3789765 {A B : Type'} (n : nat) (f : type1411 A B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term147 A B _43482 n f) = (term149 A B _43482 n f).
Proof. exact (EQ_MP (@lem3789764 A B _43482 n f) (@lem3789761 A B n f _43482 h1)). Qed.
Lemma lem3789766 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3789767 {A B : Type'} (n : nat) (f : type1411 A B) (b : B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term151 A B _43482 n f b) = (term152 A B _43482 n f b).
Proof. exact (MK_COMB (@lem3789765 A B n f _43482 h1) (@lem3789766 B b)). Qed.
Lemma lem3789768 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (f : type1411 A B) : (term152 A B _43482 n f b) = (term153 A B _43482 n b f).
Proof. exact (eq_refl (term152 A B _43482 n f b)). Qed.
Lemma lem3789769 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) : (term154 A B _43482 n f b) = (term154 A B _43482 n f b).
Proof. exact (eq_refl (term154 A B _43482 n f b)). Qed.
Lemma lem3789770 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (f : type1411 A B) : ((term151 A B _43482 n f b) = (term152 A B _43482 n f b)) = ((term151 A B _43482 n f b) = (term153 A B _43482 n b f)).
Proof. exact (MK_COMB (@lem3789769 A B _43482 n f b) (@lem3789768 A B _43482 n b f)). Qed.
Lemma lem3789771 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term151 A B _43482 n f b) = (term153 A B _43482 n b f).
Proof. exact (EQ_MP (@lem3789770 A B _43482 n b f) (@lem3789767 A B n f b _43482 h1)). Qed.
Lemma lem3789772 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3789773 {A B : Type'} (n : nat) (b : B) (f : type1411 A B) (s : A -> Prop) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term155 A B _43482 n f b s) = (term156 A B _43482 n b f s).
Proof. exact (MK_COMB (@lem3789771 A B n b f _43482 h1) (@lem3789772 A s)). Qed.
Lemma lem3789774 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) : (term156 A B _43482 n b f s) = (term157 A B _43482 n b s f).
Proof. exact (eq_refl (term156 A B _43482 n b f s)). Qed.
Lemma lem3789775 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) : (term158 A B _43482 n f b s) = (term158 A B _43482 n f b s).
Proof. exact (eq_refl (term158 A B _43482 n f b s)). Qed.
Lemma lem3789776 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) : ((term155 A B _43482 n f b s) = (term156 A B _43482 n b f s)) = ((term155 A B _43482 n f b s) = (term157 A B _43482 n b s f)).
Proof. exact (MK_COMB (@lem3789775 A B _43482 n f b s) (@lem3789774 A B _43482 n b s f)). Qed.
Lemma lem3789777 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term155 A B _43482 n f b s) = (term157 A B _43482 n b s f).
Proof. exact (EQ_MP (@lem3789776 A B _43482 n b s f) (@lem3789773 A B n b f s _43482 h1)). Qed.
Lemma lem3789778 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3789779 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (f : type1411 A B) (a : B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term68 A B _43482 n f b s a) = (term159 A B _43482 n b s f a).
Proof. exact (MK_COMB (@lem3789777 A B n b s f _43482 h1) (@lem3789778 B a)). Qed.
Lemma lem3789780 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) : (term159 A B _43482 n b s f a) = (term105 A B _43482 n b s a f).
Proof. exact (eq_refl (term159 A B _43482 n b s f a)). Qed.
Lemma lem3789781 {A B : Type'} (_43482 : type1570 A B) (n : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term70 A B _43482 n f b s a) = (term70 A B _43482 n f b s a).
Proof. exact (eq_refl (term70 A B _43482 n f b s a)). Qed.
Lemma lem3789782 {A B : Type'} (_43482 : type1570 A B) (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) : ((term68 A B _43482 n f b s a) = (term159 A B _43482 n b s f a)) = ((term68 A B _43482 n f b s a) = (term105 A B _43482 n b s a f)).
Proof. exact (MK_COMB (@lem3789781 A B _43482 n f b s a) (@lem3789780 A B _43482 n b s a f)). Qed.
Lemma lem3789783 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (f : type1411 A B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : (term68 A B _43482 n f b s a) = (term105 A B _43482 n b s a f).
Proof. exact (EQ_MP (@lem3789782 A B _43482 n b s a f) (@lem3789779 A B n b s f a _43482 h1)). Qed.
Lemma lem3789784 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (a : B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : term109 A B _43482 n b s a.
Proof. exact (fun f : type1411 A B => @lem3789783 A B n b s a f _43482 h1). Qed.
Lemma lem3789785 {A B : Type'} (n : nat) (b : B) (s : A -> Prop) (_43482 : type1570 A B) (h1 : term143 A B _43482) : term113 A B _43482 n b s.
Proof. exact (fun a : B => @lem3789784 A B n b s a _43482 h1). Qed.
Lemma lem3789786 {A B : Type'} (b : B) (s : A -> Prop) (_43482 : type1570 A B) (h1 : term143 A B _43482) : term117 A B _43482 b s.
Proof. exact (fun n : nat => @lem3789785 A B n b s _43482 h1). Qed.
Lemma lem3789787 {A B : Type'} (b : B) (_43482 : type1570 A B) (h1 : term143 A B _43482) : term121 A B _43482 b.
Proof. exact (fun s : A -> Prop => @lem3789786 A B b s _43482 h1). Qed.
Lemma lem3789788 {A B : Type'} (_43482 : type1570 A B) (h1 : term143 A B _43482) : term125 A B _43482.
Proof. exact (fun b : B => @lem3789787 A B b _43482 h1). Qed.
Lemma lem3789789 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term160 A B _43482.
Proof. exact (h1). Qed.
Lemma lem3789790 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term143 A B _43482.
Proof. exact (proj2 (@lem3789789 A B _43482 h1)). Qed.
Lemma lem3789791 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : (term128 A B _43482) = (term129 A B).
Proof. exact (proj1 (@lem3789789 A B _43482 h1)). Qed.
Lemma lem3789792 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : ((term128 A B _43482) = (term129 A B)) = (term60 A B _43482).
Proof. exact (prop_ext (fun h2 : (term128 A B _43482) = (term129 A B) => @lem3789755 A B _43482 h2) (fun h2 : term60 A B _43482 => @lem3789791 A B _43482 h1)). Qed.
Lemma lem3789793 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term60 A B _43482.
Proof. exact (EQ_MP (@lem3789792 A B _43482 h1) (@lem3789791 A B _43482 h1)). Qed.
Lemma lem3789794 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : (term143 A B _43482) = (term125 A B _43482).
Proof. exact (prop_ext (fun h2 : term143 A B _43482 => @lem3789788 A B _43482 h2) (fun h2 : term125 A B _43482 => @lem3789790 A B _43482 h1)). Qed.
Lemma lem3789795 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term125 A B _43482.
Proof. exact (EQ_MP (@lem3789794 A B _43482 h1) (@lem3789790 A B _43482 h1)). Qed.
Lemma lem3789796 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term127 A B _43482.
Proof. exact (conj (@lem3789793 A B _43482 h1) (@lem3789795 A B _43482 h1)). Qed.
Lemma lem3789797 {A : Type'} (e : A) : term161 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem3789798 {A : Type'} (e : A) : (term161 A e) = (term162 A e).
Proof. exact (eq_refl (term161 A e)). Qed.
Lemma lem3789799 {A : Type'} (e : A) : term162 A e.
Proof. exact (EQ_MP (@lem3789798 A e) (@lem3789797 A e)). Qed.
Lemma lem3789800 {A : Type'} (e : A) (f : type1423 A) : term163 A e f.
Proof. exact (@lem3789799 A e f). Qed.
Lemma lem3789801 {A : Type'} (e : A) (f : type1423 A) : (term163 A e f) = (term164 A e f).
Proof. exact (eq_refl (term163 A e f)). Qed.
Lemma lem3789802 {A : Type'} (e : A) (f : type1423 A) : term164 A e f.
Proof. exact (EQ_MP (@lem3789801 A e f) (@lem3789800 A e f)). Qed.
Lemma lem3789803 {A B : Type'} (e : type432 A B) (f : type85 A B) : term165 A B e f.
Proof. exact (@lem3789802 (type432 A B) e f). Qed.
Lemma lem3789804 {A B : Type'} : term166 A B.
Proof. exact (@lem3789803 A B (term129 A B) (term167 A B)). Qed.
Lemma lem3789805 {A B : Type'} (fn : type1570 A B) (n : nat) : (term168 A B fn n) = (term169 A B fn n).
Proof. exact (eq_refl (term168 A B fn n)). Qed.
Lemma lem3789806 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3789807 {A B : Type'} (fn : type1570 A B) (n : nat) : (term170 A B fn n) = (term171 A B fn n).
Proof. exact (MK_COMB (@lem3789805 A B fn n) (@lem3789806 n)). Qed.
Lemma lem3789808 {A B : Type'} (fn : type1570 A B) (n : nat) : (term171 A B fn n) = (term146 A B fn n).
Proof. exact (eq_refl (term171 A B fn n)). Qed.
Lemma lem3789809 {A B : Type'} (fn : type1570 A B) (n : nat) : (term170 A B fn n) = (term146 A B fn n).
Proof. exact (TRANS (@lem3789807 A B fn n) (@lem3789808 A B fn n)). Qed.
Lemma lem3789810 {A B : Type'} (fn : type1570 A B) (n : nat) : (term172 A B fn n) = (term172 A B fn n).
Proof. exact (eq_refl (term172 A B fn n)). Qed.
Lemma lem3789811 {A B : Type'} (fn : type1570 A B) (n : nat) : ((term145 A B fn n) = (term170 A B fn n)) = ((term145 A B fn n) = (term146 A B fn n)).
Proof. exact (MK_COMB (@lem3789810 A B fn n) (@lem3789809 A B fn n)). Qed.
Lemma lem3789812 {A B : Type'} (fn : type1570 A B) : (term173 A B fn) = (term174 A B fn).
Proof. exact (fun_ext (fun n : nat => @lem3789811 A B fn n)). Qed.
Lemma lem3789813 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3789814 {A B : Type'} (fn : type1570 A B) : (term175 A B fn) = (term143 A B fn).
Proof. exact (MK_COMB (@lem3789813) (@lem3789812 A B fn)). Qed.
Lemma lem3789815 {A B : Type'} (fn : type1570 A B) : (term176 A B fn) = (term176 A B fn).
Proof. exact (eq_refl (term176 A B fn)). Qed.
Lemma lem3789816 {A B : Type'} (fn : type1570 A B) : (term177 A B fn) = (term160 A B fn).
Proof. exact (MK_COMB (@lem3789815 A B fn) (@lem3789814 A B fn)). Qed.
Lemma lem3789817 {A B : Type'} : (term178 A B) = (term179 A B).
Proof. exact (fun_ext (fun fn : type1570 A B => @lem3789816 A B fn)). Qed.
Lemma lem3789818 {A B : Type'} : (@ex (nat -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Prop)) = (@ex (nat -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex (nat -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Prop))). Qed.
Lemma lem3789819 {A B : Type'} : (term166 A B) = (term180 A B).
Proof. exact (MK_COMB (@lem3789818 A B) (@lem3789817 A B)). Qed.
Lemma lem3789820 {A B : Type'} : term180 A B.
Proof. exact (EQ_MP (@lem3789819 A B) (@lem3789804 A B)). Qed.
Lemma lem3789821 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term160 A B _43482.
Proof. exact (h1). Qed.
Lemma lem3789822 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term143 A B _43482.
Proof. exact (proj2 (@lem3789821 A B _43482 h1)). Qed.
Lemma lem3789823 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : (term128 A B _43482) = (term129 A B).
Proof. exact (proj1 (@lem3789821 A B _43482 h1)). Qed.
Lemma lem3789824 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term160 A B _43482.
Proof. exact (conj (@lem3789823 A B _43482 h1) (@lem3789822 A B _43482 h1)). Qed.
Lemma lem3789825 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term180 A B.
Proof. exact (ex_intro (term179 A B) _43482 (@lem3789824 A B _43482 h1)). Qed.
Lemma lem3789826 {A B : Type'} (h1 : term180 A B) : term180 A B.
Proof. exact (h1). Qed.
Lemma lem3789827 {A B : Type'} (h1 : term180 A B) : term180 A B.
Proof. exact (ex_elim (@lem3789826 A B h1) (fun _43482 : type1570 A B => fun h0 : term179 A B _43482 => @lem3789825 A B _43482 h0)). Qed.
Lemma lem3789828 {A B : Type'} : (term180 A B) = (term180 A B).
Proof. exact (prop_ext (fun h1 : term180 A B => @lem3789827 A B h1) (fun h1 : term180 A B => @lem3789820 A B)). Qed.
Lemma lem3789829 {A B : Type'} : term180 A B.
Proof. exact (EQ_MP (@lem3789828 A B) (@lem3789820 A B)). Qed.
Lemma lem3789830 {A B : Type'} (_43482 : type1570 A B) (h1 : term160 A B _43482) : term181 A B.
Proof. exact (ex_intro (term182 A B) _43482 (@lem3789796 A B _43482 h1)). Qed.
Lemma lem3789831 {A B : Type'} (h1 : term180 A B) : term180 A B.
Proof. exact (h1). Qed.
Lemma lem3789832 {A B : Type'} (h1 : term180 A B) : term181 A B.
Proof. exact (ex_elim (@lem3789831 A B h1) (fun _43482 : type1570 A B => fun h0 : term179 A B _43482 => @lem3789830 A B _43482 h0)). Qed.
Lemma lem3789833 {A B : Type'} : (term180 A B) = (term181 A B).
Proof. exact (prop_ext (fun h1 : term180 A B => @lem3789832 A B h1) (fun h1 : term181 A B => @lem3789829 A B)). Qed.
Lemma lem3789834 {A B : Type'} : term181 A B.
Proof. exact (EQ_MP (@lem3789833 A B) (@lem3789829 A B)). Qed.
Lemma lem3789835 {A B : Type'} (_43482 : type1570 A B) (h1 : term127 A B _43482) : term127 A B _43482.
Proof. exact (h1). Qed.
Lemma lem3789836 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : FINREC' = (term4 A B _43482)) : (term127 A B _43482) = (term126 A B FINREC').
Proof. exact (SYM (@lem3789726 A B FINREC' _43482 h1)). Qed.
Lemma lem3789837 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : term127 A B _43482) (h2 : FINREC' = (term4 A B _43482)) : term126 A B FINREC'.
Proof. exact (EQ_MP (@lem3789836 A B FINREC' _43482 h2) (@lem3789835 A B _43482 h1)). Qed.
Lemma lem3789838 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : term127 A B _43482) (h2 : FINREC' = (term4 A B _43482)) : term183 A B.
Proof. exact (ex_intro (term184 A B) FINREC' (@lem3789837 A B FINREC' _43482 h1 h2)). Qed.
Lemma lem3789839 {A B : Type'} (_43482 : type1570 A B) : (term4 A B _43482) = (term4 A B _43482).
Proof. exact (eq_refl (term4 A B _43482)). Qed.
Lemma lem3789840 {A B : Type'} (FINREC' : type431 A B) (_43482 : type1570 A B) (h1 : term127 A B _43482) : term185 A B FINREC' _43482.
Proof. exact (fun h0 : FINREC' = (term4 A B _43482) => @lem3789838 A B FINREC' _43482 h1 h0). Qed.
Lemma lem3789841 {A B : Type'} (_43482 : type1570 A B) (h1 : term127 A B _43482) : term186 A B _43482.
Proof. exact (@lem3789840 A B (term4 A B _43482) _43482 h1). Qed.
Lemma lem3789842 {A B : Type'} (_43482 : type1570 A B) (h1 : term127 A B _43482) : term183 A B.
Proof. exact (@lem3789841 A B _43482 h1 (@lem3789839 A B _43482)). Qed.
Lemma lem3789843 {A B : Type'} (h1 : term181 A B) : term181 A B.
Proof. exact (h1). Qed.
Lemma lem3789844 {A B : Type'} (h1 : term181 A B) : term183 A B.
Proof. exact (ex_elim (@lem3789843 A B h1) (fun _43482 : type1570 A B => fun h0 : term182 A B _43482 => @lem3789842 A B _43482 h0)). Qed.
Lemma lem3789845 {A B : Type'} : (term181 A B) = (term183 A B).
Proof. exact (prop_ext (fun h1 : term181 A B => @lem3789844 A B h1) (fun h1 : term183 A B => @lem3789834 A B)). Qed.
Lemma lem3789846 {A B : Type'} : term183 A B.
Proof. exact (EQ_MP (@lem3789845 A B) (@lem3789834 A B)). Qed.
Lemma lem3789847 {A B : Type'} : term187 A B.
Proof. exact (fun _43486 : type1671 => @lem3789846 A B). Qed.
Lemma lem3789848 {A B : Type'} (P : type1413 A B) : term188 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem3789849 {A B : Type'} (P : type1413 A B) : (term188 A B P) = ((term189 A B P) = (term190 A B P)).
Proof. exact (eq_refl (term188 A B P)). Qed.
Lemma lem3789852 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem3789849 A B P) (@lem3789848 A B P)). Qed.
Lemma lem3789853 {A B : Type'} (P : type1261 A B) : (term191 A B P) = (term192 A B P).
Proof. exact (@lem3789852 type1671 (type431 A B) P). Qed.
Lemma lem3789854 {A B : Type'} : (term193 A B) = (term194 A B).
Proof. exact (@lem3789853 A B (term195 A B)). Qed.
Lemma lem3789855 {A B : Type'} (_43486 : type1671) : (term196 A B _43486) = (term184 A B).
Proof. exact (eq_refl (term196 A B _43486)). Qed.
Lemma lem3789856 {A B : Type'} (FINREC' : type431 A B) : FINREC' = FINREC'.
Proof. exact (eq_refl FINREC'). Qed.
Lemma lem3789857 {A B : Type'} (_43486 : type1671) (FINREC' : type431 A B) : (term197 A B _43486 FINREC') = (term198 A B FINREC').
Proof. exact (MK_COMB (@lem3789855 A B _43486) (@lem3789856 A B FINREC')). Qed.
Lemma lem3789858 {A B : Type'} (FINREC' : type431 A B) : (term198 A B FINREC') = (term126 A B FINREC').
Proof. exact (eq_refl (term198 A B FINREC')). Qed.
Lemma lem3789859 {A B : Type'} (_43486 : type1671) (FINREC' : type431 A B) : (term197 A B _43486 FINREC') = (term126 A B FINREC').
Proof. exact (TRANS (@lem3789857 A B _43486 FINREC') (@lem3789858 A B FINREC')). Qed.
Lemma lem3789860 {A B : Type'} (_43486 : type1671) : (term199 A B _43486) = (term184 A B).
Proof. exact (fun_ext (fun FINREC' : type431 A B => @lem3789859 A B _43486 FINREC')). Qed.
Lemma lem3789861 {A B : Type'} : (@ex ((A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop)) = (@ex ((A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789862 {A B : Type'} (_43486 : type1671) : (term200 A B _43486) = (term183 A B).
Proof. exact (MK_COMB (@lem3789861 A B) (@lem3789860 A B _43486)). Qed.
Lemma lem3789863 {A B : Type'} : (term201 A B) = (term202 A B).
Proof. exact (fun_ext (fun _43486 : type1671 => @lem3789862 A B _43486)). Qed.
Lemma lem3789864 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem3789865 {A B : Type'} : (term193 A B) = (term187 A B).
Proof. exact (MK_COMB (@lem3789864) (@lem3789863 A B)). Qed.
Lemma lem3789866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3789867 {A B : Type'} : (term203 A B) = (term204 A B).
Proof. exact (MK_COMB (@lem3789866) (@lem3789865 A B)). Qed.
Lemma lem3789868 {A B : Type'} (_43486 : type1671) : (term196 A B _43486) = (term184 A B).
Proof. exact (eq_refl (term196 A B _43486)). Qed.
Lemma lem3789869 {A B : Type'} (FINREC' : type1266 A B) (_43486 : type1671) : (FINREC' _43486) = (FINREC' _43486).
Proof. exact (eq_refl (FINREC' _43486)). Qed.
Lemma lem3789870 {A B : Type'} (FINREC' : type1266 A B) (_43486 : type1671) : (term205 A B FINREC' _43486) = (term206 A B FINREC' _43486).
Proof. exact (MK_COMB (@lem3789868 A B _43486) (@lem3789869 A B FINREC' _43486)). Qed.
Lemma lem3789871 {A B : Type'} (FINREC' : type1266 A B) (_43486 : type1671) : (term206 A B FINREC' _43486) = (term207 A B FINREC' _43486).
Proof. exact (eq_refl (term206 A B FINREC' _43486)). Qed.
Lemma lem3789872 {A B : Type'} (FINREC' : type1266 A B) (_43486 : type1671) : (term205 A B FINREC' _43486) = (term207 A B FINREC' _43486).
Proof. exact (TRANS (@lem3789870 A B FINREC' _43486) (@lem3789871 A B FINREC' _43486)). Qed.
Lemma lem3789873 {A B : Type'} (FINREC' : type1266 A B) : (term208 A B FINREC') = (term209 A B FINREC').
Proof. exact (fun_ext (fun _43486 : type1671 => @lem3789872 A B FINREC' _43486)). Qed.
Lemma lem3789874 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem3789875 {A B : Type'} (FINREC' : type1266 A B) : (term210 A B FINREC') = (term211 A B FINREC').
Proof. exact (MK_COMB (@lem3789874) (@lem3789873 A B FINREC')). Qed.
Lemma lem3789876 {A B : Type'} : (term212 A B) = (term213 A B).
Proof. exact (fun_ext (fun FINREC' : type1266 A B => @lem3789875 A B FINREC')). Qed.
Lemma lem3789877 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop))). Qed.
Lemma lem3789878 {A B : Type'} : (term194 A B) = (term214 A B).
Proof. exact (MK_COMB (@lem3789877 A B) (@lem3789876 A B)). Qed.
Lemma lem3789879 {A B : Type'} : ((term193 A B) = (term194 A B)) = ((term187 A B) = (term214 A B)).
Proof. exact (MK_COMB (@lem3789867 A B) (@lem3789878 A B)). Qed.
Lemma lem3789880 {A B : Type'} : (term187 A B) = (term214 A B).
Proof. exact (EQ_MP (@lem3789879 A B) (@lem3789854 A B)). Qed.
Lemma lem3789881 {A B : Type'} : term214 A B.
Proof. exact (EQ_MP (@lem3789880 A B) (@lem3789847 A B)). Qed.
Lemma lem3789883 {A : Type'} : (@ex A) = (term215 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem3789884 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> nat -> Prop)) = (term216 A B).
Proof. exact (@lem3789883 (type1266 A B)). Qed.
Lemma lem3789885 {A B : Type'} : (term213 A B) = (term213 A B).
Proof. exact (eq_refl (term213 A B)). Qed.
Lemma lem3789886 {A B : Type'} : (term214 A B) = (term217 A B).
Proof. exact (MK_COMB (@lem3789884 A B) (@lem3789885 A B)). Qed.
Lemma lem3789887 {A B : Type'} : (term217 A B) = (term218 A B).
Proof. exact (eq_refl (term217 A B)). Qed.
Lemma lem3789888 {A B : Type'} : (term214 A B) = (term218 A B).
Proof. exact (TRANS (@lem3789886 A B) (@lem3789887 A B)). Qed.
Lemma lem3789889 {A B : Type'} : term218 A B.
Proof. exact (EQ_MP (@lem3789888 A B) (@lem3789881 A B)). Qed.
