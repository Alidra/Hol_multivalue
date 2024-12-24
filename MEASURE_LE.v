Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEASURE_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LTE_TRANS_spec.
Require Import LT_REFL_spec.
Require Import MEASURE_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem365463 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem365464 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem365465 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem365464 t1) (@lem365463 t1)). Qed.
Lemma lem365466 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem365465 t1 t2). Qed.
Lemma lem365467 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem365468 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem365467 t1 t2) (@lem365466 t1 t2)). Qed.
Lemma lem365469 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem365468 t1 t2 t3). Qed.
Lemma lem365470 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem365471 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem365470 t1 t2 t3) (@lem365469 t1 t2 t3)). Qed.
Lemma lem365472 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem365471 t1 t2 t3)). Qed.
Lemma lem365473 {_16406 : Type'} (m : _16406 -> nat) : term7 _16406 m.
Proof. exact (@lem365417 _16406 m). Qed.
Lemma lem365474 {_16406 : Type'} (m : _16406 -> nat) : (term7 _16406 m) = ((@MEASURE _16406 m) = (term8 _16406 m)).
Proof. exact (eq_refl (term7 _16406 m)). Qed.
Lemma lem365485 {_16406 : Type'} (m : _16406 -> nat) : (@MEASURE _16406 m) = (term8 _16406 m).
Proof. exact (EQ_MP (@lem365474 _16406 m) (@lem365473 _16406 m)). Qed.
Lemma lem365486 {_16436 : Type'} (m : _16436 -> nat) : (@MEASURE _16436 m) = (term8 _16436 m).
Proof. exact (@lem365485 _16436 m). Qed.
Lemma lem365487 {_16436 : Type'} (y : _16436) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem365488 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (@MEASURE _16436 m y) = (term9 _16436 m y).
Proof. exact (MK_COMB (@lem365486 _16436 m) (@lem365487 _16436 y)). Qed.
Lemma lem365490 {A B : Type'} (f : A -> B) (y : A) : (term10 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem365491 {_16436 : Type'} (f : type1402 _16436) (y : _16436) : (term11 _16436 f y) = (f y).
Proof. exact (@lem365490 _16436 (_16436 -> Prop) f y). Qed.
Lemma lem365492 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term12 _16436 m y) = (term9 _16436 m y).
Proof. exact (@lem365491 _16436 (term8 _16436 m) y). Qed.
Lemma lem365493 {_16436 : Type'} (x : _16436) (m : _16436 -> nat) : (term9 _16436 m x) = (term13 _16436 x m).
Proof. exact (eq_refl (term9 _16436 m x)). Qed.
Lemma lem365494 {_16436 : Type'} (m : _16436 -> nat) : (term14 _16436 m) = (term8 _16436 m).
Proof. exact (fun_ext (fun x : _16436 => @lem365493 _16436 x m)). Qed.
Lemma lem365495 {_16436 : Type'} (y : _16436) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem365496 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term12 _16436 m y) = (term9 _16436 m y).
Proof. exact (MK_COMB (@lem365494 _16436 m) (@lem365495 _16436 y)). Qed.
Lemma lem365497 {_16436 : Type'} : (@eq (_16436 -> Prop)) = (@eq (_16436 -> Prop)).
Proof. exact (eq_refl (@eq (_16436 -> Prop))). Qed.
Lemma lem365498 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term15 _16436 m y) = (term16 _16436 m y).
Proof. exact (MK_COMB (@lem365497 _16436) (@lem365496 _16436 m y)). Qed.
Lemma lem365499 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term9 _16436 m y) = (term13 _16436 y m).
Proof. exact (eq_refl (term9 _16436 m y)). Qed.
Lemma lem365500 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : ((term12 _16436 m y) = (term9 _16436 m y)) = ((term9 _16436 m y) = (term13 _16436 y m)).
Proof. exact (MK_COMB (@lem365498 _16436 m y) (@lem365499 _16436 y m)). Qed.
Lemma lem365501 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term9 _16436 m y) = (term13 _16436 y m).
Proof. exact (EQ_MP (@lem365500 _16436 y m) (@lem365492 _16436 m y)). Qed.
Lemma lem365502 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (@MEASURE _16436 m y) = (term13 _16436 y m).
Proof. exact (TRANS (@lem365488 _16436 m y) (@lem365501 _16436 y m)). Qed.
Lemma lem365503 {_16436 : Type'} (a : _16436) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem365504 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (@MEASURE _16436 m y a) = (term17 _16436 y m a).
Proof. exact (MK_COMB (@lem365502 _16436 y m) (@lem365503 _16436 a)). Qed.
Lemma lem365506 {A B : Type'} (f : A -> B) (y : A) : (term10 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem365507 {_16436 : Type'} (f : _16436 -> Prop) (y : _16436) : (term18 _16436 f y) = (f y).
Proof. exact (@lem365506 _16436 Prop f y). Qed.
Lemma lem365508 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term19 _16436 y m a) = (term17 _16436 y m a).
Proof. exact (@lem365507 _16436 (term13 _16436 y m) a). Qed.
Lemma lem365509 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (y' : _16436) : (term17 _16436 y m y') = (term20 _16436 y m y').
Proof. exact (eq_refl (term17 _16436 y m y')). Qed.
Lemma lem365510 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term21 _16436 y m) = (term13 _16436 y m).
Proof. exact (fun_ext (fun y' : _16436 => @lem365509 _16436 y m y')). Qed.
Lemma lem365511 {_16436 : Type'} (a : _16436) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem365512 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term19 _16436 y m a) = (term17 _16436 y m a).
Proof. exact (MK_COMB (@lem365510 _16436 y m) (@lem365511 _16436 a)). Qed.
Lemma lem365513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365514 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term22 _16436 y m a) = (term23 _16436 y m a).
Proof. exact (MK_COMB (@lem365513) (@lem365512 _16436 y m a)). Qed.
Lemma lem365515 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term17 _16436 y m a) = (term20 _16436 y m a).
Proof. exact (eq_refl (term17 _16436 y m a)). Qed.
Lemma lem365516 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : ((term19 _16436 y m a) = (term17 _16436 y m a)) = ((term17 _16436 y m a) = (term20 _16436 y m a)).
Proof. exact (MK_COMB (@lem365514 _16436 y m a) (@lem365515 _16436 y m a)). Qed.
Lemma lem365517 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term17 _16436 y m a) = (term20 _16436 y m a).
Proof. exact (EQ_MP (@lem365516 _16436 y m a) (@lem365508 _16436 y m a)). Qed.
Lemma lem365518 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (@MEASURE _16436 m y a) = (term20 _16436 y m a).
Proof. exact (TRANS (@lem365504 _16436 y m a) (@lem365517 _16436 y m a)). Qed.
Lemma lem365519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365520 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term24 _16436 m y a) = (term25 _16436 y m a).
Proof. exact (MK_COMB (@lem365519) (@lem365518 _16436 y m a)). Qed.
Lemma lem365522 {_16406 : Type'} (m : _16406 -> nat) : (@MEASURE _16406 m) = (term8 _16406 m).
Proof. exact (EQ_MP (@lem365474 _16406 m) (@lem365473 _16406 m)). Qed.
Lemma lem365523 {_16436 : Type'} (m : _16436 -> nat) : (@MEASURE _16436 m) = (term8 _16436 m).
Proof. exact (@lem365522 _16436 m). Qed.
Lemma lem365524 {_16436 : Type'} (y : _16436) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem365525 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (@MEASURE _16436 m y) = (term9 _16436 m y).
Proof. exact (MK_COMB (@lem365523 _16436 m) (@lem365524 _16436 y)). Qed.
Lemma lem365527 {A B : Type'} (f : A -> B) (y : A) : (term10 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem365528 {_16436 : Type'} (f : type1402 _16436) (y : _16436) : (term11 _16436 f y) = (f y).
Proof. exact (@lem365527 _16436 (_16436 -> Prop) f y). Qed.
Lemma lem365529 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term12 _16436 m y) = (term9 _16436 m y).
Proof. exact (@lem365528 _16436 (term8 _16436 m) y). Qed.
Lemma lem365530 {_16436 : Type'} (x : _16436) (m : _16436 -> nat) : (term9 _16436 m x) = (term13 _16436 x m).
Proof. exact (eq_refl (term9 _16436 m x)). Qed.
Lemma lem365531 {_16436 : Type'} (m : _16436 -> nat) : (term14 _16436 m) = (term8 _16436 m).
Proof. exact (fun_ext (fun x : _16436 => @lem365530 _16436 x m)). Qed.
Lemma lem365532 {_16436 : Type'} (y : _16436) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem365533 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term12 _16436 m y) = (term9 _16436 m y).
Proof. exact (MK_COMB (@lem365531 _16436 m) (@lem365532 _16436 y)). Qed.
Lemma lem365534 {_16436 : Type'} : (@eq (_16436 -> Prop)) = (@eq (_16436 -> Prop)).
Proof. exact (eq_refl (@eq (_16436 -> Prop))). Qed.
Lemma lem365535 {_16436 : Type'} (m : _16436 -> nat) (y : _16436) : (term15 _16436 m y) = (term16 _16436 m y).
Proof. exact (MK_COMB (@lem365534 _16436) (@lem365533 _16436 m y)). Qed.
Lemma lem365536 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term9 _16436 m y) = (term13 _16436 y m).
Proof. exact (eq_refl (term9 _16436 m y)). Qed.
Lemma lem365537 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : ((term12 _16436 m y) = (term9 _16436 m y)) = ((term9 _16436 m y) = (term13 _16436 y m)).
Proof. exact (MK_COMB (@lem365535 _16436 m y) (@lem365536 _16436 y m)). Qed.
Lemma lem365538 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term9 _16436 m y) = (term13 _16436 y m).
Proof. exact (EQ_MP (@lem365537 _16436 y m) (@lem365529 _16436 m y)). Qed.
Lemma lem365539 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (@MEASURE _16436 m y) = (term13 _16436 y m).
Proof. exact (TRANS (@lem365525 _16436 m y) (@lem365538 _16436 y m)). Qed.
Lemma lem365540 {_16436 : Type'} (b : _16436) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem365541 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (@MEASURE _16436 m y b) = (term17 _16436 y m b).
Proof. exact (MK_COMB (@lem365539 _16436 y m) (@lem365540 _16436 b)). Qed.
Lemma lem365543 {A B : Type'} (f : A -> B) (y : A) : (term10 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem365544 {_16436 : Type'} (f : _16436 -> Prop) (y : _16436) : (term18 _16436 f y) = (f y).
Proof. exact (@lem365543 _16436 Prop f y). Qed.
Lemma lem365545 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term19 _16436 y m b) = (term17 _16436 y m b).
Proof. exact (@lem365544 _16436 (term13 _16436 y m) b). Qed.
Lemma lem365546 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (y' : _16436) : (term17 _16436 y m y') = (term20 _16436 y m y').
Proof. exact (eq_refl (term17 _16436 y m y')). Qed.
Lemma lem365547 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) : (term21 _16436 y m) = (term13 _16436 y m).
Proof. exact (fun_ext (fun y' : _16436 => @lem365546 _16436 y m y')). Qed.
Lemma lem365548 {_16436 : Type'} (b : _16436) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem365549 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term19 _16436 y m b) = (term17 _16436 y m b).
Proof. exact (MK_COMB (@lem365547 _16436 y m) (@lem365548 _16436 b)). Qed.
Lemma lem365550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365551 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term22 _16436 y m b) = (term23 _16436 y m b).
Proof. exact (MK_COMB (@lem365550) (@lem365549 _16436 y m b)). Qed.
Lemma lem365552 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term17 _16436 y m b) = (term20 _16436 y m b).
Proof. exact (eq_refl (term17 _16436 y m b)). Qed.
Lemma lem365553 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : ((term19 _16436 y m b) = (term17 _16436 y m b)) = ((term17 _16436 y m b) = (term20 _16436 y m b)).
Proof. exact (MK_COMB (@lem365551 _16436 y m b) (@lem365552 _16436 y m b)). Qed.
Lemma lem365554 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term17 _16436 y m b) = (term20 _16436 y m b).
Proof. exact (EQ_MP (@lem365553 _16436 y m b) (@lem365545 _16436 y m b)). Qed.
Lemma lem365555 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (@MEASURE _16436 m y b) = (term20 _16436 y m b).
Proof. exact (TRANS (@lem365541 _16436 y m b) (@lem365554 _16436 y m b)). Qed.
Lemma lem365556 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term26 _16436 a m y b) = (term27 _16436 a y m b).
Proof. exact (MK_COMB (@lem365520 _16436 y m a) (@lem365555 _16436 y m b)). Qed.
Lemma lem365559 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term28 _16436 a m b) = (term29 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365556 _16436 a y m b)). Qed.
Lemma lem365560 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365561 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term30 _16436 a m b) = (term31 _16436 a m b).
Proof. exact (MK_COMB (@lem365560 _16436) (@lem365559 _16436 a m b)). Qed.
Lemma lem365566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365567 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term32 _16436 a m b) = (term33 _16436 a m b).
Proof. exact (MK_COMB (@lem365566) (@lem365561 _16436 a m b)). Qed.
Lemma lem365568 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term34 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (eq_refl (term34 _16436 a m b)). Qed.
Lemma lem365569 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term30 _16436 a m b) = (term34 _16436 a m b)) = ((term31 _16436 a m b) = (term34 _16436 a m b)).
Proof. exact (MK_COMB (@lem365567 _16436 a m b) (@lem365568 _16436 a m b)). Qed.
Lemma lem365572 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term31 _16436 a m b) = (term34 _16436 a m b)) = ((term30 _16436 a m b) = (term34 _16436 a m b)).
Proof. exact (SYM (@lem365569 _16436 a m b)). Qed.
Lemma lem365574 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem365575 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term31 _16436 a m b) = (term34 _16436 a m b)) = (term36 _16436 a m b).
Proof. exact (@lem365574 ((term31 _16436 a m b) = (term34 _16436 a m b))). Qed.
Lemma lem365576 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term36 _16436 a m b) = ((term31 _16436 a m b) = (term34 _16436 a m b)).
Proof. exact (SYM (@lem365575 _16436 a m b)). Qed.
Lemma lem365577 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term37 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365580 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term38 _16436 a m b) : term38 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365581 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term39 _16436 a m b.
Proof. exact (fun h0 : term38 _16436 a m b => @lem365580 _16436 a m b h0). Qed.
Lemma lem365582 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term39 _16436 a m b) : term39 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365583 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term38 _16436 a m b) : term38 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365584 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term38 _16436 a m b) (h2 : term39 _16436 a m b) : term38 _16436 a m b.
Proof. exact (@lem365582 _16436 a m b h2 (@lem365583 _16436 a m b h1)). Qed.
Lemma lem365585 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term38 _16436 a m b) : term40 _16436 a m b.
Proof. exact (fun h0 : term39 _16436 a m b => @lem365584 _16436 a m b h1 h0). Qed.
Lemma lem365586 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term39 _16436 a m b) : term39 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365587 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term38 _16436 a m b) (h2 : term39 _16436 a m b) : term38 _16436 a m b.
Proof. exact (@lem365585 _16436 a m b h1 (@lem365586 _16436 a m b h2)). Qed.
Lemma lem365588 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term39 _16436 a m b) : term39 _16436 a m b.
Proof. exact (fun h0 : term38 _16436 a m b => @lem365587 _16436 a m b h0 h1). Qed.
Lemma lem365589 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term41 _16436 a m b.
Proof. exact (fun h0 : term39 _16436 a m b => @lem365588 _16436 a m b h0). Qed.
Lemma lem365592 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term39 _16436 a m b.
Proof. exact (@lem365589 _16436 a m b (@lem365581 _16436 a m b)). Qed.
Lemma lem365593 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term39 _16436 a m b.
Proof. exact (@lem365592 _16436 a m b). Qed.
Lemma lem365639 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem365640 : term42 = term43.
Proof. exact (@lem365639 term44). Qed.
Lemma lem365649 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem365650 : term46 = term47.
Proof. exact (MK_COMB (@lem365649) (@lem365640)). Qed.
Lemma lem365653 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem365654 : term49 = term50.
Proof. exact (MK_COMB (@lem365653) (@lem365650)). Qed.
Lemma lem365657 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term51 _16436 a m b) = (term51 _16436 a m b).
Proof. exact (eq_refl (term51 _16436 a m b)). Qed.
Lemma lem365658 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term38 _16436 a m b) = (term52 _16436 a m b).
Proof. exact (MK_COMB (@lem365657 _16436 a m b) (@lem365654)). Qed.
Lemma lem365661 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term53 _16436 m b) = (term54 _16436 m b).
Proof. exact (fun_ext (fun a : _16436 => @lem365658 _16436 a m b)). Qed.
Lemma lem365662 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365663 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term55 _16436 m b) = (term56 _16436 m b).
Proof. exact (MK_COMB (@lem365662 _16436) (@lem365661 _16436 m b)). Qed.
Lemma lem365668 {_16436 : Type'} (b : _16436) : (term57 _16436 b) = (term58 _16436 b).
Proof. exact (fun_ext (fun m : _16436 -> nat => @lem365663 _16436 m b)). Qed.
Lemma lem365669 {_16436 : Type'} : (@all (_16436 -> nat)) = (@all (_16436 -> nat)).
Proof. exact (eq_refl (@all (_16436 -> nat))). Qed.
Lemma lem365670 {_16436 : Type'} (b : _16436) : (term59 _16436 b) = (term60 _16436 b).
Proof. exact (MK_COMB (@lem365669 _16436) (@lem365668 _16436 b)). Qed.
Lemma lem365675 {_16436 : Type'} : (term61 _16436) = (term62 _16436).
Proof. exact (fun_ext (fun b : _16436 => @lem365670 _16436 b)). Qed.
Lemma lem365676 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365685 {_16436 : Type'} : (term63 _16436) = (term64 _16436).
Proof. exact (MK_COMB (@lem365676 _16436) (@lem365675 _16436)). Qed.
Lemma lem365692 (n : nat) (m : nat) : ((term65 m n) = (Peano.lt n m)) = ((term65 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term65 m n) = (Peano.lt n m))). Qed.
Lemma lem365693 (m : nat) : (term66 m) = (term66 m).
Proof. exact (fun_ext (fun n : nat => @lem365692 n m)). Qed.
Lemma lem365694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365695 (m : nat) : (term67 m) = (term67 m).
Proof. exact (MK_COMB (@lem365694) (@lem365693 m)). Qed.
Lemma lem365696 : term68 = term68.
Proof. exact (fun_ext (fun m : nat => @lem365695 m)). Qed.
Lemma lem365697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365698 : term44 = term44.
Proof. exact (MK_COMB (@lem365697) (@lem365696)). Qed.
Lemma lem365699 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem365700 : term43 = term43.
Proof. exact (MK_COMB (@lem365699) (@lem365698)). Qed.
Lemma lem365709 (n : nat) (m : nat) (p : nat) : (term69 n m p) = (term69 n m p).
Proof. exact (eq_refl (term69 n m p)). Qed.
Lemma lem365710 (n : nat) (m : nat) : (term70 n m) = (term70 n m).
Proof. exact (fun_ext (fun p : nat => @lem365709 n m p)). Qed.
Lemma lem365711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365712 (n : nat) (m : nat) : (term71 n m) = (term71 n m).
Proof. exact (MK_COMB (@lem365711) (@lem365710 n m)). Qed.
Lemma lem365713 (m : nat) : (term72 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem365712 n m)). Qed.
Lemma lem365714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365715 (m : nat) : (term73 m) = (term73 m).
Proof. exact (MK_COMB (@lem365714) (@lem365713 m)). Qed.
Lemma lem365716 : term74 = term74.
Proof. exact (fun_ext (fun m : nat => @lem365715 m)). Qed.
Lemma lem365717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365718 : term75 = term75.
Proof. exact (MK_COMB (@lem365717) (@lem365716)). Qed.
Lemma lem365719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365720 : term45 = term45.
Proof. exact (MK_COMB (@lem365719) (@lem365718)). Qed.
Lemma lem365721 : term47 = term47.
Proof. exact (MK_COMB (@lem365720) (@lem365700)). Qed.
Lemma lem365724 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem365725 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem365724 n)). Qed.
Lemma lem365726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem365727 : term78 = term78.
Proof. exact (MK_COMB (@lem365726) (@lem365725)). Qed.
Lemma lem365728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365729 : term48 = term48.
Proof. exact (MK_COMB (@lem365728) (@lem365727)). Qed.
Lemma lem365730 : term50 = term50.
Proof. exact (MK_COMB (@lem365729) (@lem365721)). Qed.
Lemma lem365731 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term34 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (eq_refl (term34 _16436 a m b)). Qed.
Lemma lem365736 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term27 _16436 a y m b) = (term27 _16436 a y m b).
Proof. exact (eq_refl (term27 _16436 a y m b)). Qed.
Lemma lem365737 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term29 _16436 a m b) = (term29 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365736 _16436 a y m b)). Qed.
Lemma lem365738 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365739 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term31 _16436 a m b) = (term31 _16436 a m b).
Proof. exact (MK_COMB (@lem365738 _16436) (@lem365737 _16436 a m b)). Qed.
Lemma lem365740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365741 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term33 _16436 a m b) = (term33 _16436 a m b).
Proof. exact (MK_COMB (@lem365740) (@lem365739 _16436 a m b)). Qed.
Lemma lem365742 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term31 _16436 a m b) = (term34 _16436 a m b)) = ((term31 _16436 a m b) = (term34 _16436 a m b)).
Proof. exact (MK_COMB (@lem365741 _16436 a m b) (@lem365731 _16436 a m b)). Qed.
Lemma lem365743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem365744 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term37 _16436 a m b) = (term37 _16436 a m b).
Proof. exact (MK_COMB (@lem365743) (@lem365742 _16436 a m b)). Qed.
Lemma lem365745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365746 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term51 _16436 a m b) = (term51 _16436 a m b).
Proof. exact (MK_COMB (@lem365745) (@lem365744 _16436 a m b)). Qed.
Lemma lem365747 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term52 _16436 a m b) = (term52 _16436 a m b).
Proof. exact (MK_COMB (@lem365746 _16436 a m b) (@lem365730)). Qed.
Lemma lem365748 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term54 _16436 m b) = (term54 _16436 m b).
Proof. exact (fun_ext (fun a : _16436 => @lem365747 _16436 a m b)). Qed.
Lemma lem365749 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365750 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term56 _16436 m b) = (term56 _16436 m b).
Proof. exact (MK_COMB (@lem365749 _16436) (@lem365748 _16436 m b)). Qed.
Lemma lem365751 {_16436 : Type'} (b : _16436) : (term58 _16436 b) = (term58 _16436 b).
Proof. exact (fun_ext (fun m : _16436 -> nat => @lem365750 _16436 m b)). Qed.
Lemma lem365752 {_16436 : Type'} : (@all (_16436 -> nat)) = (@all (_16436 -> nat)).
Proof. exact (eq_refl (@all (_16436 -> nat))). Qed.
Lemma lem365753 {_16436 : Type'} (b : _16436) : (term60 _16436 b) = (term60 _16436 b).
Proof. exact (MK_COMB (@lem365752 _16436) (@lem365751 _16436 b)). Qed.
Lemma lem365754 {_16436 : Type'} : (term62 _16436) = (term62 _16436).
Proof. exact (fun_ext (fun b : _16436 => @lem365753 _16436 b)). Qed.
Lemma lem365755 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365756 {_16436 : Type'} : (term64 _16436) = (term64 _16436).
Proof. exact (MK_COMB (@lem365755 _16436) (@lem365754 _16436)). Qed.
Lemma lem365831 {_16436 : Type'} : (term63 _16436) = (term64 _16436).
Proof. exact (TRANS (@lem365685 _16436) (@lem365756 _16436)). Qed.
Lemma lem365832 {_16436 : Type'} : (term64 _16436) = (term63 _16436).
Proof. exact (SYM (@lem365831 _16436)). Qed.
Lemma lem365833 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term37 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem365834 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem365835 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem365836 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem365845 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term79 _16436 a y m b) = (term80 _16436 a y m b).
Proof. exact (@lem17362 (term20 _16436 y m a) (term20 _16436 y m b)). Qed.
Lemma lem365850 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term27 _16436 a y m b) = (term81 _16436 a y m b).
Proof. exact (@lem17265 (term20 _16436 y m a) (term20 _16436 y m b)). Qed.
Lemma lem365851 {_16436 : Type'} (P : _16436 -> Prop) : (term82 _16436 P) = (term83 _16436 P).
Proof. exact (@lem18392 _16436 P). Qed.
Lemma lem365852 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term84 _16436 a m b) = (term85 _16436 a m b).
Proof. exact (@lem365851 _16436 (term29 _16436 a m b)). Qed.
Lemma lem365853 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term86 _16436 a m b y) = (term27 _16436 a y m b).
Proof. exact (eq_refl (term86 _16436 a m b y)). Qed.
Lemma lem365854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem365855 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term87 _16436 a m b y) = (term79 _16436 a y m b).
Proof. exact (MK_COMB (@lem365854) (@lem365853 _16436 a y m b)). Qed.
Lemma lem365856 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term87 _16436 a m b y) = (term80 _16436 a y m b).
Proof. exact (TRANS (@lem365855 _16436 a y m b) (@lem365845 _16436 a y m b)). Qed.
Lemma lem365857 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term88 _16436 a m b) = (term89 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365856 _16436 a y m b)). Qed.
Lemma lem365858 {_16436 : Type'} : (@ex _16436) = (@ex _16436).
Proof. exact (eq_refl (@ex _16436)). Qed.
Lemma lem365859 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term85 _16436 a m b) = (term90 _16436 a m b).
Proof. exact (MK_COMB (@lem365858 _16436) (@lem365857 _16436 a m b)). Qed.
Lemma lem365860 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term84 _16436 a m b) = (term90 _16436 a m b).
Proof. exact (TRANS (@lem365852 _16436 a m b) (@lem365859 _16436 a m b)). Qed.
Lemma lem365861 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term29 _16436 a m b) = (term91 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365850 _16436 a y m b)). Qed.
Lemma lem365862 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem365863 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term31 _16436 a m b) = (term92 _16436 a m b).
Proof. exact (MK_COMB (@lem365862 _16436) (@lem365861 _16436 a m b)). Qed.
Lemma lem365864 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term93 _16436 a m b) = (term93 _16436 a m b).
Proof. exact (eq_refl (term93 _16436 a m b)). Qed.
Lemma lem365865 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term34 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (eq_refl (term34 _16436 a m b)). Qed.
Lemma lem365866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem365867 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term94 _16436 a m b) = (term95 _16436 a m b).
Proof. exact (MK_COMB (@lem365866) (@lem365860 _16436 a m b)). Qed.
Lemma lem365868 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term96 _16436 a m b) = (term97 _16436 a m b).
Proof. exact (MK_COMB (@lem365867 _16436 a m b) (@lem365865 _16436 a m b)). Qed.
Lemma lem365869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem365870 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term98 _16436 a m b) = (term99 _16436 a m b).
Proof. exact (MK_COMB (@lem365869) (@lem365863 _16436 a m b)). Qed.
Lemma lem365871 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term100 _16436 a m b) = (term101 _16436 a m b).
Proof. exact (MK_COMB (@lem365870 _16436 a m b) (@lem365864 _16436 a m b)). Qed.
Lemma lem365872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem365873 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term102 _16436 a m b) = (term103 _16436 a m b).
Proof. exact (MK_COMB (@lem365872) (@lem365871 _16436 a m b)). Qed.
Lemma lem365874 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term104 _16436 a m b) = (term105 _16436 a m b).
Proof. exact (MK_COMB (@lem365873 _16436 a m b) (@lem365868 _16436 a m b)). Qed.
Lemma lem365875 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term37 _16436 a m b) = (term104 _16436 a m b).
Proof. exact (@lem17646 (term31 _16436 a m b) (term34 _16436 a m b)). Qed.
Lemma lem365876 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term37 _16436 a m b) = (term105 _16436 a m b).
Proof. exact (TRANS (@lem365875 _16436 a m b) (@lem365874 _16436 a m b)). Qed.
Lemma lem365975 {A : Type'} (P : A -> Prop) (Q : Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem365976 {_16436 : Type'} (P : _16436 -> Prop) (Q : Prop) : (term106 _16436 P Q) = (term107 _16436 P Q).
Proof. exact (@lem365975 _16436 P Q). Qed.
Lemma lem365977 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term108 _16436 a m b) = (term109 _16436 a m b).
Proof. exact (@lem365976 _16436 (term89 _16436 a m b) (term34 _16436 a m b)). Qed.
Lemma lem365978 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term110 _16436 a m b y) = (term80 _16436 a y m b).
Proof. exact (eq_refl (term110 _16436 a m b y)). Qed.
Lemma lem365979 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term111 _16436 a m b) = (term89 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365978 _16436 a y m b)). Qed.
Lemma lem365980 {_16436 : Type'} : (@ex _16436) = (@ex _16436).
Proof. exact (eq_refl (@ex _16436)). Qed.
Lemma lem365981 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term112 _16436 a m b) = (term90 _16436 a m b).
Proof. exact (MK_COMB (@lem365980 _16436) (@lem365979 _16436 a m b)). Qed.
Lemma lem365982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem365983 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term113 _16436 a m b) = (term95 _16436 a m b).
Proof. exact (MK_COMB (@lem365982) (@lem365981 _16436 a m b)). Qed.
Lemma lem365984 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term34 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (eq_refl (term34 _16436 a m b)). Qed.
Lemma lem365985 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term108 _16436 a m b) = (term97 _16436 a m b).
Proof. exact (MK_COMB (@lem365983 _16436 a m b) (@lem365984 _16436 a m b)). Qed.
Lemma lem365986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365987 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term114 _16436 a m b) = (term115 _16436 a m b).
Proof. exact (MK_COMB (@lem365986) (@lem365985 _16436 a m b)). Qed.
Lemma lem365988 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term110 _16436 a m b y) = (term80 _16436 a y m b).
Proof. exact (eq_refl (term110 _16436 a m b y)). Qed.
Lemma lem365989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem365990 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term116 _16436 a m b y) = (term117 _16436 a y m b).
Proof. exact (MK_COMB (@lem365989) (@lem365988 _16436 a y m b)). Qed.
Lemma lem365991 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term34 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (eq_refl (term34 _16436 a m b)). Qed.
Lemma lem365992 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term118 _16436 y a m b) = (term119 _16436 y a m b).
Proof. exact (MK_COMB (@lem365990 _16436 a y m b) (@lem365991 _16436 a m b)). Qed.
Lemma lem365993 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term120 _16436 a m b) = (term121 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem365992 _16436 y a m b)). Qed.
Lemma lem365994 {_16436 : Type'} : (@ex _16436) = (@ex _16436).
Proof. exact (eq_refl (@ex _16436)). Qed.
Lemma lem365995 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term109 _16436 a m b) = (term122 _16436 a m b).
Proof. exact (MK_COMB (@lem365994 _16436) (@lem365993 _16436 a m b)). Qed.
Lemma lem365996 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term108 _16436 a m b) = (term109 _16436 a m b)) = ((term97 _16436 a m b) = (term122 _16436 a m b)).
Proof. exact (MK_COMB (@lem365987 _16436 a m b) (@lem365995 _16436 a m b)). Qed.
Lemma lem365997 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term97 _16436 a m b) = (term122 _16436 a m b).
Proof. exact (EQ_MP (@lem365996 _16436 a m b) (@lem365977 _16436 a m b)). Qed.
Lemma lem365998 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term103 _16436 a m b) = (term103 _16436 a m b).
Proof. exact (eq_refl (term103 _16436 a m b)). Qed.
Lemma lem365999 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term105 _16436 a m b) = (term123 _16436 a m b).
Proof. exact (MK_COMB (@lem365998 _16436 a m b) (@lem365997 _16436 a m b)). Qed.
Lemma lem366001 {A : Type'} (P : Prop) (Q : A -> Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem366002 {_16436 : Type'} (P : Prop) (Q : _16436 -> Prop) : (term124 _16436 P Q) = (term125 _16436 P Q).
Proof. exact (@lem366001 _16436 P Q). Qed.
Lemma lem366003 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term126 _16436 a m b) = (term127 _16436 a m b).
Proof. exact (@lem366002 _16436 (term101 _16436 a m b) (term121 _16436 a m b)). Qed.
Lemma lem366004 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term128 _16436 a m b y) = (term119 _16436 y a m b).
Proof. exact (eq_refl (term128 _16436 a m b y)). Qed.
Lemma lem366005 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term129 _16436 a m b) = (term121 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem366004 _16436 y a m b)). Qed.
Lemma lem366006 {_16436 : Type'} : (@ex _16436) = (@ex _16436).
Proof. exact (eq_refl (@ex _16436)). Qed.
Lemma lem366007 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term130 _16436 a m b) = (term122 _16436 a m b).
Proof. exact (MK_COMB (@lem366006 _16436) (@lem366005 _16436 a m b)). Qed.
Lemma lem366008 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term103 _16436 a m b) = (term103 _16436 a m b).
Proof. exact (eq_refl (term103 _16436 a m b)). Qed.
Lemma lem366009 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term126 _16436 a m b) = (term123 _16436 a m b).
Proof. exact (MK_COMB (@lem366008 _16436 a m b) (@lem366007 _16436 a m b)). Qed.
Lemma lem366010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem366011 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term131 _16436 a m b) = (term132 _16436 a m b).
Proof. exact (MK_COMB (@lem366010) (@lem366009 _16436 a m b)). Qed.
Lemma lem366012 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term128 _16436 a m b y) = (term119 _16436 y a m b).
Proof. exact (eq_refl (term128 _16436 a m b y)). Qed.
Lemma lem366013 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term103 _16436 a m b) = (term103 _16436 a m b).
Proof. exact (eq_refl (term103 _16436 a m b)). Qed.
Lemma lem366014 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term133 _16436 a m b y) = (term134 _16436 y a m b).
Proof. exact (MK_COMB (@lem366013 _16436 a m b) (@lem366012 _16436 y a m b)). Qed.
Lemma lem366015 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term135 _16436 a m b) = (term136 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem366014 _16436 y a m b)). Qed.
Lemma lem366016 {_16436 : Type'} : (@ex _16436) = (@ex _16436).
Proof. exact (eq_refl (@ex _16436)). Qed.
Lemma lem366017 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term127 _16436 a m b) = (term137 _16436 a m b).
Proof. exact (MK_COMB (@lem366016 _16436) (@lem366015 _16436 a m b)). Qed.
Lemma lem366018 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : ((term126 _16436 a m b) = (term127 _16436 a m b)) = ((term123 _16436 a m b) = (term137 _16436 a m b)).
Proof. exact (MK_COMB (@lem366011 _16436 a m b) (@lem366017 _16436 a m b)). Qed.
Lemma lem366019 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term123 _16436 a m b) = (term137 _16436 a m b).
Proof. exact (EQ_MP (@lem366018 _16436 a m b) (@lem366003 _16436 a m b)). Qed.
Lemma lem366021 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term105 _16436 a m b) = (term137 _16436 a m b).
Proof. exact (TRANS (@lem365999 _16436 a m b) (@lem366019 _16436 a m b)). Qed.
Lemma lem366022 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term37 _16436 a m b) = (term137 _16436 a m b).
Proof. exact (TRANS (@lem365876 _16436 a m b) (@lem366021 _16436 a m b)). Qed.
Lemma lem366023 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term137 _16436 a m b.
Proof. exact (EQ_MP (@lem366022 _16436 a m b) (@lem365833 _16436 a m b h1)). Qed.
Lemma lem366024 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem366025 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem366024 n)). Qed.
Lemma lem366026 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366035 : term78 = term78.
Proof. exact (MK_COMB (@lem366026) (@lem366025)). Qed.
Lemma lem366036 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem366035) (@lem365834 h1)). Qed.
Lemma lem366043 (m : nat) (n : nat) (p : nat) : (term138 m n p) = (term139 m n p).
Proof. exact (@lem17045 (Peano.lt m n) (Peano.le n p)). Qed.
Lemma lem366044 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem366045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem366046 (m : nat) (n : nat) (p : nat) : (term140 m n p) = (term141 m n p).
Proof. exact (MK_COMB (@lem366045) (@lem366043 m n p)). Qed.
Lemma lem366047 (n : nat) (m : nat) (p : nat) : (term142 n m p) = (term143 n m p).
Proof. exact (MK_COMB (@lem366046 m n p) (@lem366044 m p)). Qed.
Lemma lem366048 (n : nat) (m : nat) (p : nat) : (term69 n m p) = (term142 n m p).
Proof. exact (@lem17265 (term144 m n p) (Peano.lt m p)). Qed.
Lemma lem366049 (n : nat) (m : nat) (p : nat) : (term69 n m p) = (term143 n m p).
Proof. exact (TRANS (@lem366048 n m p) (@lem366047 n m p)). Qed.
Lemma lem366050 (n : nat) (m : nat) : (term70 n m) = (term145 n m).
Proof. exact (fun_ext (fun p : nat => @lem366049 n m p)). Qed.
Lemma lem366051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366052 (n : nat) (m : nat) : (term71 n m) = (term146 n m).
Proof. exact (MK_COMB (@lem366051) (@lem366050 n m)). Qed.
Lemma lem366053 (m : nat) : (term72 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem366052 n m)). Qed.
Lemma lem366054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366055 (m : nat) : (term73 m) = (term148 m).
Proof. exact (MK_COMB (@lem366054) (@lem366053 m)). Qed.
Lemma lem366056 : term74 = term149.
Proof. exact (fun_ext (fun m : nat => @lem366055 m)). Qed.
Lemma lem366057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366118 : term75 = term150.
Proof. exact (MK_COMB (@lem366057) (@lem366056)). Qed.
Lemma lem366119 (h1 : term75) : term150.
Proof. exact (EQ_MP (@lem366118) (@lem365835 h1)). Qed.
Lemma lem366123 (m : nat) (n : nat) : (term151 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem366125 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem366126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem366127 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (MK_COMB (@lem366126) (@lem366123 m n)). Qed.
Lemma lem366128 (n : nat) (m : nat) : (term154 n m) = (term155 n m).
Proof. exact (MK_COMB (@lem366127 m n) (@lem366125 n m)). Qed.
Lemma lem366133 (n : nat) (m : nat) : (term156 n m) = (term156 n m).
Proof. exact (eq_refl (term156 n m)). Qed.
Lemma lem366134 (n : nat) (m : nat) : (term157 n m) = (term158 n m).
Proof. exact (MK_COMB (@lem366133 n m) (@lem366128 n m)). Qed.
Lemma lem366135 (n : nat) (m : nat) : ((term65 m n) = (Peano.lt n m)) = (term157 n m).
Proof. exact (@lem17784 (term65 m n) (Peano.lt n m)). Qed.
Lemma lem366136 (n : nat) (m : nat) : ((term65 m n) = (Peano.lt n m)) = (term158 n m).
Proof. exact (TRANS (@lem366135 n m) (@lem366134 n m)). Qed.
Lemma lem366137 (m : nat) : (term66 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem366136 n m)). Qed.
Lemma lem366138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366139 (m : nat) : (term67 m) = (term160 m).
Proof. exact (MK_COMB (@lem366138) (@lem366137 m)). Qed.
Lemma lem366140 : term68 = term161.
Proof. exact (fun_ext (fun m : nat => @lem366139 m)). Qed.
Lemma lem366141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366142 : term44 = term162.
Proof. exact (MK_COMB (@lem366141) (@lem366140)). Qed.
Lemma lem366148 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem366149 (P : nat -> Prop) (Q : nat -> Prop) : (term165 P Q) = (term166 P Q).
Proof. exact (@lem366148 nat P Q). Qed.
Lemma lem366150 (m : nat) : (term167 m) = (term168 m).
Proof. exact (@lem366149 (term169 m) (term170 m)). Qed.
Lemma lem366151 (n : nat) (m : nat) : (term171 m n) = (term172 n m).
Proof. exact (eq_refl (term171 m n)). Qed.
Lemma lem366152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366153 (n : nat) (m : nat) : (term173 m n) = (term156 n m).
Proof. exact (MK_COMB (@lem366152) (@lem366151 n m)). Qed.
Lemma lem366154 (n : nat) (m : nat) : (term174 m n) = (term155 n m).
Proof. exact (eq_refl (term174 m n)). Qed.
Lemma lem366155 (n : nat) (m : nat) : (term175 m n) = (term158 n m).
Proof. exact (MK_COMB (@lem366153 n m) (@lem366154 n m)). Qed.
Lemma lem366156 (m : nat) : (term176 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem366155 n m)). Qed.
Lemma lem366157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366158 (m : nat) : (term167 m) = (term160 m).
Proof. exact (MK_COMB (@lem366157) (@lem366156 m)). Qed.
Lemma lem366159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem366160 (m : nat) : (term177 m) = (term178 m).
Proof. exact (MK_COMB (@lem366159) (@lem366158 m)). Qed.
Lemma lem366161 (n : nat) (m : nat) : (term171 m n) = (term172 n m).
Proof. exact (eq_refl (term171 m n)). Qed.
Lemma lem366162 (m : nat) : (term179 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem366161 n m)). Qed.
Lemma lem366163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366164 (m : nat) : (term180 m) = (term181 m).
Proof. exact (MK_COMB (@lem366163) (@lem366162 m)). Qed.
Lemma lem366165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366166 (m : nat) : (term182 m) = (term183 m).
Proof. exact (MK_COMB (@lem366165) (@lem366164 m)). Qed.
Lemma lem366167 (n : nat) (m : nat) : (term174 m n) = (term155 n m).
Proof. exact (eq_refl (term174 m n)). Qed.
Lemma lem366168 (m : nat) : (term184 m) = (term170 m).
Proof. exact (fun_ext (fun n : nat => @lem366167 n m)). Qed.
Lemma lem366169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366170 (m : nat) : (term185 m) = (term186 m).
Proof. exact (MK_COMB (@lem366169) (@lem366168 m)). Qed.
Lemma lem366171 (m : nat) : (term168 m) = (term187 m).
Proof. exact (MK_COMB (@lem366166 m) (@lem366170 m)). Qed.
Lemma lem366172 (m : nat) : ((term167 m) = (term168 m)) = ((term160 m) = (term187 m)).
Proof. exact (MK_COMB (@lem366160 m) (@lem366171 m)). Qed.
Lemma lem366173 (m : nat) : (term160 m) = (term187 m).
Proof. exact (EQ_MP (@lem366172 m) (@lem366150 m)). Qed.
Lemma lem366270 : term161 = term188.
Proof. exact (fun_ext (fun m : nat => @lem366173 m)). Qed.
Lemma lem366271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366272 : term162 = term189.
Proof. exact (MK_COMB (@lem366271) (@lem366270)). Qed.
Lemma lem366274 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem366275 (P : nat -> Prop) (Q : nat -> Prop) : (term165 P Q) = (term166 P Q).
Proof. exact (@lem366274 nat P Q). Qed.
Lemma lem366276 : term190 = term191.
Proof. exact (@lem366275 term192 term193). Qed.
Lemma lem366277 (m : nat) : (term194 m) = (term181 m).
Proof. exact (eq_refl (term194 m)). Qed.
Lemma lem366278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366279 (m : nat) : (term195 m) = (term183 m).
Proof. exact (MK_COMB (@lem366278) (@lem366277 m)). Qed.
Lemma lem366280 (m : nat) : (term196 m) = (term186 m).
Proof. exact (eq_refl (term196 m)). Qed.
Lemma lem366281 (m : nat) : (term197 m) = (term187 m).
Proof. exact (MK_COMB (@lem366279 m) (@lem366280 m)). Qed.
Lemma lem366282 : term198 = term188.
Proof. exact (fun_ext (fun m : nat => @lem366281 m)). Qed.
Lemma lem366283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366284 : term190 = term189.
Proof. exact (MK_COMB (@lem366283) (@lem366282)). Qed.
Lemma lem366285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem366286 : term199 = term200.
Proof. exact (MK_COMB (@lem366285) (@lem366284)). Qed.
Lemma lem366287 (m : nat) : (term194 m) = (term181 m).
Proof. exact (eq_refl (term194 m)). Qed.
Lemma lem366288 : term201 = term192.
Proof. exact (fun_ext (fun m : nat => @lem366287 m)). Qed.
Lemma lem366289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366290 : term202 = term203.
Proof. exact (MK_COMB (@lem366289) (@lem366288)). Qed.
Lemma lem366291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366292 : term204 = term205.
Proof. exact (MK_COMB (@lem366291) (@lem366290)). Qed.
Lemma lem366293 (m : nat) : (term196 m) = (term186 m).
Proof. exact (eq_refl (term196 m)). Qed.
Lemma lem366294 : term206 = term193.
Proof. exact (fun_ext (fun m : nat => @lem366293 m)). Qed.
Lemma lem366295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366296 : term207 = term208.
Proof. exact (MK_COMB (@lem366295) (@lem366294)). Qed.
Lemma lem366297 : term191 = term209.
Proof. exact (MK_COMB (@lem366292) (@lem366296)). Qed.
Lemma lem366298 : (term190 = term191) = (term189 = term209).
Proof. exact (MK_COMB (@lem366286) (@lem366297)). Qed.
Lemma lem366299 : term189 = term209.
Proof. exact (EQ_MP (@lem366298) (@lem366276)). Qed.
Lemma lem366406 : term162 = term209.
Proof. exact (TRANS (@lem366272) (@lem366299)). Qed.
Lemma lem366407 : term44 = term209.
Proof. exact (TRANS (@lem366142) (@lem366406)). Qed.
Lemma lem366408 (h1 : term44) : term209.
Proof. exact (EQ_MP (@lem366407) (@lem365836 h1)). Qed.
Lemma lem366409 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term134 _16436 y a m b) : term134 _16436 y a m b.
Proof. exact (h1). Qed.
Lemma lem366416 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem366417 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem366416 n)). Qed.
Lemma lem366418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366419 : term78 = term78.
Proof. exact (MK_COMB (@lem366418) (@lem366417)). Qed.
Lemma lem366420 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem366419) (@lem366036 h1)). Qed.
Lemma lem366445 (n : nat) (m : nat) (p : nat) : (term143 n m p) = (term143 n m p).
Proof. exact (eq_refl (term143 n m p)). Qed.
Lemma lem366446 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (fun_ext (fun p : nat => @lem366445 n m p)). Qed.
Lemma lem366447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366448 (n : nat) (m : nat) : (term146 n m) = (term146 n m).
Proof. exact (MK_COMB (@lem366447) (@lem366446 n m)). Qed.
Lemma lem366449 (m : nat) : (term147 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem366448 n m)). Qed.
Lemma lem366450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366451 (m : nat) : (term148 m) = (term148 m).
Proof. exact (MK_COMB (@lem366450) (@lem366449 m)). Qed.
Lemma lem366452 : term149 = term149.
Proof. exact (fun_ext (fun m : nat => @lem366451 m)). Qed.
Lemma lem366453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366454 : term150 = term150.
Proof. exact (MK_COMB (@lem366453) (@lem366452)). Qed.
Lemma lem366455 (h1 : term75) : term150.
Proof. exact (EQ_MP (@lem366454) (@lem366119 h1)). Qed.
Lemma lem366468 (n : nat) (m : nat) : (term155 n m) = (term155 n m).
Proof. exact (eq_refl (term155 n m)). Qed.
Lemma lem366469 (m : nat) : (term170 m) = (term170 m).
Proof. exact (fun_ext (fun n : nat => @lem366468 n m)). Qed.
Lemma lem366470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366471 (m : nat) : (term186 m) = (term186 m).
Proof. exact (MK_COMB (@lem366470) (@lem366469 m)). Qed.
Lemma lem366472 : term193 = term193.
Proof. exact (fun_ext (fun m : nat => @lem366471 m)). Qed.
Lemma lem366473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366474 : term208 = term208.
Proof. exact (MK_COMB (@lem366473) (@lem366472)). Qed.
Lemma lem366491 (n : nat) (m : nat) : (term172 n m) = (term172 n m).
Proof. exact (eq_refl (term172 n m)). Qed.
Lemma lem366492 (m : nat) : (term169 m) = (term169 m).
Proof. exact (fun_ext (fun n : nat => @lem366491 n m)). Qed.
Lemma lem366493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366494 (m : nat) : (term181 m) = (term181 m).
Proof. exact (MK_COMB (@lem366493) (@lem366492 m)). Qed.
Lemma lem366495 : term192 = term192.
Proof. exact (fun_ext (fun m : nat => @lem366494 m)). Qed.
Lemma lem366496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366497 : term203 = term203.
Proof. exact (MK_COMB (@lem366496) (@lem366495)). Qed.
Lemma lem366498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366499 : term205 = term205.
Proof. exact (MK_COMB (@lem366498) (@lem366497)). Qed.
Lemma lem366500 : term209 = term209.
Proof. exact (MK_COMB (@lem366499) (@lem366474)). Qed.
Lemma lem366501 (h1 : term44) : term209.
Proof. exact (EQ_MP (@lem366500) (@lem366408 h1)). Qed.
Lemma lem366536 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term119 _16436 y a m b) = (term119 _16436 y a m b).
Proof. exact (eq_refl (term119 _16436 y a m b)). Qed.
Lemma lem366547 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term93 _16436 a m b) = (term93 _16436 a m b).
Proof. exact (eq_refl (term93 _16436 a m b)). Qed.
Lemma lem366570 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term81 _16436 a y m b) = (term81 _16436 a y m b).
Proof. exact (eq_refl (term81 _16436 a y m b)). Qed.
Lemma lem366571 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term91 _16436 a m b) = (term91 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem366570 _16436 a y m b)). Qed.
Lemma lem366572 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem366573 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term92 _16436 a m b) = (term92 _16436 a m b).
Proof. exact (MK_COMB (@lem366572 _16436) (@lem366571 _16436 a m b)). Qed.
Lemma lem366574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem366575 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term99 _16436 a m b) = (term99 _16436 a m b).
Proof. exact (MK_COMB (@lem366574) (@lem366573 _16436 a m b)). Qed.
Lemma lem366576 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term101 _16436 a m b) = (term101 _16436 a m b).
Proof. exact (MK_COMB (@lem366575 _16436 a m b) (@lem366547 _16436 a m b)). Qed.
Lemma lem366577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem366578 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term103 _16436 a m b) = (term103 _16436 a m b).
Proof. exact (MK_COMB (@lem366577) (@lem366576 _16436 a m b)). Qed.
Lemma lem366579 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) : (term134 _16436 y a m b) = (term134 _16436 y a m b).
Proof. exact (MK_COMB (@lem366578 _16436 a m b) (@lem366536 _16436 y a m b)). Qed.
Lemma lem366580 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term134 _16436 y a m b) : term134 _16436 y a m b.
Proof. exact (EQ_MP (@lem366579 _16436 y a m b) (@lem366409 _16436 y a m b h1)). Qed.
Lemma lem366581 (h1 : term44) : term208.
Proof. exact (proj2 (@lem366501 h1)). Qed.
Lemma lem366583 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term101 _16436 a m b.
Proof. exact (h1). Qed.
Lemma lem366584 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term119 _16436 y a m b.
Proof. exact (h1). Qed.
Lemma lem366586 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term92 _16436 a m b.
Proof. exact (proj1 (@lem366583 _16436 a m b h1)). Qed.
Lemma lem366588 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term80 _16436 a y m b.
Proof. exact (proj1 (@lem366584 _16436 y a m b h1)). Qed.
Lemma lem366592 (n : nat) : (term76 n) = (term76 n).
Proof. exact (eq_refl (term76 n)). Qed.
Lemma lem366593 : term77 = term77.
Proof. exact (fun_ext (fun n : nat => @lem366592 n)). Qed.
Lemma lem366594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366596 : term78 = term78.
Proof. exact (MK_COMB (@lem366594) (@lem366593)). Qed.
Lemma lem366597 (h1 : term78) : term78.
Proof. exact (EQ_MP (@lem366596) (@lem366420 h1)). Qed.
Lemma lem366646 (n : nat) (m : nat) : (term155 n m) = (term155 n m).
Proof. exact (eq_refl (term155 n m)). Qed.
Lemma lem366647 (m : nat) : (term170 m) = (term170 m).
Proof. exact (fun_ext (fun n : nat => @lem366646 n m)). Qed.
Lemma lem366648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366649 (m : nat) : (term186 m) = (term186 m).
Proof. exact (MK_COMB (@lem366648) (@lem366647 m)). Qed.
Lemma lem366650 : term193 = term193.
Proof. exact (fun_ext (fun m : nat => @lem366649 m)). Qed.
Lemma lem366651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366653 : term208 = term208.
Proof. exact (MK_COMB (@lem366651) (@lem366650)). Qed.
Lemma lem366654 (h1 : term44) : term208.
Proof. exact (EQ_MP (@lem366653) (@lem366581 h1)). Qed.
Lemma lem366662 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) : (term81 _16436 a y m b) = (term81 _16436 a y m b).
Proof. exact (eq_refl (term81 _16436 a y m b)). Qed.
Lemma lem366663 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term91 _16436 a m b) = (term91 _16436 a m b).
Proof. exact (fun_ext (fun y : _16436 => @lem366662 _16436 a y m b)). Qed.
Lemma lem366664 {_16436 : Type'} : (@all _16436) = (@all _16436).
Proof. exact (eq_refl (@all _16436)). Qed.
Lemma lem366666 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term92 _16436 a m b) = (term92 _16436 a m b).
Proof. exact (MK_COMB (@lem366664 _16436) (@lem366663 _16436 a m b)). Qed.
Lemma lem366667 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term92 _16436 a m b.
Proof. exact (EQ_MP (@lem366666 _16436 a m b) (@lem366586 _16436 a m b h1)). Qed.
Lemma lem366692 (n : nat) (m : nat) (p : nat) : (term143 n m p) = (term143 n m p).
Proof. exact (eq_refl (term143 n m p)). Qed.
Lemma lem366693 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (fun_ext (fun p : nat => @lem366692 n m p)). Qed.
Lemma lem366694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366695 (n : nat) (m : nat) : (term146 n m) = (term146 n m).
Proof. exact (MK_COMB (@lem366694) (@lem366693 n m)). Qed.
Lemma lem366696 (m : nat) : (term147 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem366695 n m)). Qed.
Lemma lem366697 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366698 (m : nat) : (term148 m) = (term148 m).
Proof. exact (MK_COMB (@lem366697) (@lem366696 m)). Qed.
Lemma lem366699 : term149 = term149.
Proof. exact (fun_ext (fun m : nat => @lem366698 m)). Qed.
Lemma lem366700 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem366702 : term150 = term150.
Proof. exact (MK_COMB (@lem366700) (@lem366699)). Qed.
Lemma lem366703 (h1 : term75) : term150.
Proof. exact (EQ_MP (@lem366702) (@lem366455 h1)). Qed.
Lemma lem366748 (_7936 : nat) (h1 : term78) : term210 _7936.
Proof. exact (@lem366597 h1 _7936). Qed.
Lemma lem366749 (_7936 : nat) : (term210 _7936) = (term76 _7936).
Proof. exact (eq_refl (term210 _7936)). Qed.
Lemma lem366766 (_7942 : nat) (h1 : term44) : term196 _7942.
Proof. exact (@lem366654 h1 _7942). Qed.
Lemma lem366767 (_7942 : nat) : (term196 _7942) = (term186 _7942).
Proof. exact (eq_refl (term196 _7942)). Qed.
Lemma lem366768 (_7942 : nat) (h1 : term44) : term186 _7942.
Proof. exact (EQ_MP (@lem366767 _7942) (@lem366766 _7942 h1)). Qed.
Lemma lem366769 (_7942 : nat) (_7943 : nat) (h1 : term44) : term174 _7942 _7943.
Proof. exact (@lem366768 _7942 h1 _7943). Qed.
Lemma lem366770 (_7943 : nat) (_7942 : nat) : (term174 _7942 _7943) = (term155 _7943 _7942).
Proof. exact (eq_refl (term174 _7942 _7943)). Qed.
Lemma lem366772 {_16436 : Type'} (_7944 : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term211 _16436 a m b _7944.
Proof. exact (@lem366667 _16436 a m b h1 _7944). Qed.
Lemma lem366773 {_16436 : Type'} (a : _16436) (_7944 : _16436) (m : _16436 -> nat) (b : _16436) : (term211 _16436 a m b _7944) = (term81 _16436 a _7944 m b).
Proof. exact (eq_refl (term211 _16436 a m b _7944)). Qed.
Lemma lem366778 (_7946 : nat) (h1 : term75) : term212 _7946.
Proof. exact (@lem366703 h1 _7946). Qed.
Lemma lem366779 (_7946 : nat) : (term212 _7946) = (term148 _7946).
Proof. exact (eq_refl (term212 _7946)). Qed.
Lemma lem366780 (_7946 : nat) (h1 : term75) : term148 _7946.
Proof. exact (EQ_MP (@lem366779 _7946) (@lem366778 _7946 h1)). Qed.
Lemma lem366781 (_7946 : nat) (_7947 : nat) (h1 : term75) : term213 _7946 _7947.
Proof. exact (@lem366780 _7946 h1 _7947). Qed.
Lemma lem366782 (_7947 : nat) (_7946 : nat) : (term213 _7946 _7947) = (term146 _7947 _7946).
Proof. exact (eq_refl (term213 _7946 _7947)). Qed.
Lemma lem366783 (_7947 : nat) (_7946 : nat) (h1 : term75) : term146 _7947 _7946.
Proof. exact (EQ_MP (@lem366782 _7947 _7946) (@lem366781 _7946 _7947 h1)). Qed.
Lemma lem366784 (_7947 : nat) (_7946 : nat) (_7948 : nat) (h1 : term75) : term214 _7947 _7946 _7948.
Proof. exact (@lem366783 _7947 _7946 h1 _7948). Qed.
Lemma lem366785 (_7947 : nat) (_7946 : nat) (_7948 : nat) : (term214 _7947 _7946 _7948) = (term143 _7947 _7946 _7948).
Proof. exact (eq_refl (term214 _7947 _7946 _7948)). Qed.
Lemma lem366786 (_7947 : nat) (_7946 : nat) (_7948 : nat) (h1 : term75) : term143 _7947 _7946 _7948.
Proof. exact (EQ_MP (@lem366785 _7947 _7946 _7948) (@lem366784 _7947 _7946 _7948 h1)). Qed.
Lemma lem366824 (_7943 : nat) (_7942 : nat) (h1 : term44) : term155 _7943 _7942.
Proof. exact (EQ_MP (@lem366770 _7943 _7942) (@lem366769 _7942 _7943 h1)). Qed.
Lemma lem366830 {_16436 : Type'} (_7944 : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term81 _16436 a _7944 m b.
Proof. exact (EQ_MP (@lem366773 _16436 a _7944 m b) (@lem366772 _16436 _7944 a m b h1)). Qed.
Lemma lem366832 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term93 _16436 a m b.
Proof. exact (proj2 (@lem366583 _16436 a m b h1)). Qed.
Lemma lem366845 (_7947 : nat) (_7946 : nat) (_7948 : nat) : (term143 _7947 _7946 _7948) = (term215 _7947 _7946 _7948).
Proof. exact (@lem365472 (term216 _7946 _7947) (term65 _7947 _7948) (Peano.lt _7946 _7948)). Qed.
Lemma lem366846 (_7947 : nat) (_7946 : nat) (_7948 : nat) (h1 : term75) : term215 _7947 _7946 _7948.
Proof. exact (EQ_MP (@lem366845 _7947 _7946 _7948) (@lem366786 _7947 _7946 _7948 h1)). Qed.
Lemma lem366864 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term217 _16436 y m b.
Proof. exact (proj2 (@lem366588 _16436 y a m b h1)). Qed.
Lemma lem366866 (_7936 : nat) (h1 : term78) : term76 _7936.
Proof. exact (EQ_MP (@lem366749 _7936) (@lem366748 _7936 h1)). Qed.
Lemma lem366867 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) (h1 : term78) : term218 _16436 m b.
Proof. exact (@lem366866 (m b) h1). Qed.
Lemma lem366868 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) (h1 : term78) : term219 _16436 m b.
Proof. exact (fun h0 : term220 _16436 m b => @lem366867 _16436 m b h1). Qed.
Lemma lem366870 (p : Prop) : (term221 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem366871 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term219 _16436 m b) = (term218 _16436 m b).
Proof. exact (@lem366870 (term220 _16436 m b)). Qed.
Lemma lem366872 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) (h1 : term78) : term218 _16436 m b.
Proof. exact (EQ_MP (@lem366871 _16436 m b) (@lem366868 _16436 m b h1)). Qed.
Lemma lem366874 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem366877 {_16436 : Type'} (b : _16436) (_7944 : _16436) (m : _16436 -> nat) (a : _16436) : (term81 _16436 a _7944 m b) = (term223 _16436 b _7944 m a).
Proof. exact (@lem366874 (term20 _16436 _7944 m b) (term217 _16436 _7944 m a)). Qed.
Lemma lem366880 {_16436 : Type'} (_7944 : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term223 _16436 b _7944 m a.
Proof. exact (EQ_MP (@lem366877 _16436 b _7944 m a) (@lem366830 _16436 _7944 a m b h1)). Qed.
Lemma lem366881 {_16436 : Type'} (_7944 : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term223 _16436 b _7944 m a.
Proof. exact (@lem366880 _16436 _7944 a m b h1). Qed.
Lemma lem366882 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term224 _16436 b m a.
Proof. exact (@lem366881 _16436 b a m b h1). Qed.
Lemma lem366885 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term78) (h2 : term101 _16436 a m b) : term217 _16436 b m a.
Proof. exact (@lem366882 _16436 a m b h2 (@lem366872 _16436 m b h1)). Qed.
Lemma lem366886 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term78) (h2 : term101 _16436 a m b) : term225 _16436 b m a.
Proof. exact (fun h0 : term20 _16436 b m a => @lem366885 _16436 a m b h1 h2). Qed.
Lemma lem366888 (p : Prop) : (term221 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem366889 {_16436 : Type'} (b : _16436) (m : _16436 -> nat) (a : _16436) : (term225 _16436 b m a) = (term217 _16436 b m a).
Proof. exact (@lem366888 (term20 _16436 b m a)). Qed.
Lemma lem366890 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term78) (h2 : term101 _16436 a m b) : term217 _16436 b m a.
Proof. exact (EQ_MP (@lem366889 _16436 b m a) (@lem366886 _16436 a m b h1 h2)). Qed.
Lemma lem366892 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem366895 (_7942 : nat) (_7943 : nat) : (term155 _7943 _7942) = (term226 _7942 _7943).
Proof. exact (@lem366892 (Peano.lt _7943 _7942) (Peano.le _7942 _7943)). Qed.
Lemma lem366898 (_7942 : nat) (_7943 : nat) (h1 : term44) : term226 _7942 _7943.
Proof. exact (EQ_MP (@lem366895 _7942 _7943) (@lem366824 _7943 _7942 h1)). Qed.
Lemma lem366899 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) : term227 _16436 a m b.
Proof. exact (@lem366898 (m a) (m b) h1). Qed.
Lemma lem366902 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : term34 _16436 a m b.
Proof. exact (@lem366899 _16436 a m b h1 (@lem366890 _16436 a m b h2 h3)). Qed.
Lemma lem366903 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : term228 _16436 a m b.
Proof. exact (fun h0 : term93 _16436 a m b => @lem366902 _16436 a m b h1 h2 h3). Qed.
Lemma lem366905 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem366906 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term228 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (@lem366905 (term34 _16436 a m b)). Qed.
Lemma lem366907 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : term34 _16436 a m b.
Proof. exact (EQ_MP (@lem366906 _16436 a m b) (@lem366903 _16436 a m b h1 h2 h3)). Qed.
Lemma lem366910 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem366912 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term93 _16436 a m b) = (term230 _16436 a m b).
Proof. exact (@lem366910 (term34 _16436 a m b)). Qed.
Lemma lem366915 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term101 _16436 a m b) : term230 _16436 a m b.
Proof. exact (EQ_MP (@lem366912 _16436 a m b) (@lem366832 _16436 a m b h1)). Qed.
Lemma lem366918 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : False.
Proof. exact (@lem366915 _16436 a m b h3 (@lem366907 _16436 a m b h1 h2 h3)). Qed.
Lemma lem366919 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : term231.
Proof. exact (fun h0 : ~ False => @lem366918 _16436 a m b h1 h2 h3). Qed.
Lemma lem366921 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem366922 : term231 = False.
Proof. exact (@lem366921 False). Qed.
Lemma lem366923 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : False.
Proof. exact (EQ_MP (@lem366922) (@lem366919 _16436 a m b h1 h2 h3)). Qed.
Lemma lem366925 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term20 _16436 y m a.
Proof. exact (proj1 (@lem366588 _16436 y a m b h1)). Qed.
Lemma lem366926 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term232 _16436 y m a.
Proof. exact (fun h0 : term217 _16436 y m a => @lem366925 _16436 y a m b h1). Qed.
Lemma lem366928 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem366929 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (a : _16436) : (term232 _16436 y m a) = (term20 _16436 y m a).
Proof. exact (@lem366928 (term20 _16436 y m a)). Qed.
Lemma lem366930 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term20 _16436 y m a.
Proof. exact (EQ_MP (@lem366929 _16436 y m a) (@lem366926 _16436 y a m b h1)). Qed.
Lemma lem366932 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term34 _16436 a m b.
Proof. exact (proj2 (@lem366584 _16436 y a m b h1)). Qed.
Lemma lem366933 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term228 _16436 a m b.
Proof. exact (fun h0 : term93 _16436 a m b => @lem366932 _16436 y a m b h1). Qed.
Lemma lem366935 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem366936 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term228 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (@lem366935 (term34 _16436 a m b)). Qed.
Lemma lem366937 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term34 _16436 a m b.
Proof. exact (EQ_MP (@lem366936 _16436 a m b) (@lem366933 _16436 y a m b h1)). Qed.
Lemma lem366953 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem366954 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term233 _7947 _7946 _7948) = (term234 _7946 _7947 _7948).
Proof. exact (@lem366953 (Peano.lt _7946 _7948) (term65 _7947 _7948)). Qed.
Lemma lem366960 (_7946 : nat) (_7947 : nat) : (term235 _7946 _7947) = (term235 _7946 _7947).
Proof. exact (eq_refl (term235 _7946 _7947)). Qed.
Lemma lem366961 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term215 _7947 _7946 _7948) = (term236 _7946 _7947 _7948).
Proof. exact (MK_COMB (@lem366960 _7946 _7947) (@lem366954 _7946 _7947 _7948)). Qed.
Lemma lem366965 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem366966 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term236 _7946 _7947 _7948) = (term237 _7946 _7947 _7948).
Proof. exact (@lem366965 (Peano.lt _7946 _7948) (term216 _7946 _7947) (term65 _7947 _7948)). Qed.
Lemma lem366982 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term215 _7947 _7946 _7948) = (term237 _7946 _7947 _7948).
Proof. exact (TRANS (@lem366961 _7946 _7947 _7948) (@lem366966 _7946 _7947 _7948)). Qed.
Lemma lem366983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem366984 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term238 _7947 _7946 _7948) = (term239 _7946 _7947 _7948).
Proof. exact (MK_COMB (@lem366983) (@lem366982 _7946 _7947 _7948)). Qed.
Lemma lem367000 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term237 _7946 _7947 _7948) = (term237 _7946 _7947 _7948).
Proof. exact (eq_refl (term237 _7946 _7947 _7948)). Qed.
Lemma lem367001 (_7946 : nat) (_7947 : nat) (_7948 : nat) : ((term215 _7947 _7946 _7948) = (term237 _7946 _7947 _7948)) = ((term237 _7946 _7947 _7948) = (term237 _7946 _7947 _7948)).
Proof. exact (MK_COMB (@lem366984 _7946 _7947 _7948) (@lem367000 _7946 _7947 _7948)). Qed.
Lemma lem367003 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem367004 (x : Prop) : (x = x) = True.
Proof. exact (@lem367003 Prop x). Qed.
Lemma lem367005 (_7946 : nat) (_7947 : nat) (_7948 : nat) : ((term237 _7946 _7947 _7948) = (term237 _7946 _7947 _7948)) = True.
Proof. exact (@lem367004 (term237 _7946 _7947 _7948)). Qed.
Lemma lem367006 (_7946 : nat) (_7947 : nat) (_7948 : nat) : ((term215 _7947 _7946 _7948) = (term237 _7946 _7947 _7948)) = True.
Proof. exact (TRANS (@lem367001 _7946 _7947 _7948) (@lem367005 _7946 _7947 _7948)). Qed.
Lemma lem367007 (_7946 : nat) (_7947 : nat) (_7948 : nat) : True = ((term215 _7947 _7946 _7948) = (term237 _7946 _7947 _7948)).
Proof. exact (SYM (@lem367006 _7946 _7947 _7948)). Qed.
Lemma lem367008 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term215 _7947 _7946 _7948) = (term237 _7946 _7947 _7948).
Proof. exact (EQ_MP (@lem367007 _7946 _7947 _7948) (@lem0)). Qed.
Lemma lem367009 (_7946 : nat) (_7947 : nat) (_7948 : nat) (h1 : term75) : term237 _7946 _7947 _7948.
Proof. exact (EQ_MP (@lem367008 _7946 _7947 _7948) (@lem366846 _7947 _7946 _7948 h1)). Qed.
Lemma lem367011 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem367012 (_7947 : nat) (_7946 : nat) (_7948 : nat) : (term237 _7946 _7947 _7948) = (term240 _7947 _7946 _7948).
Proof. exact (@lem367011 (term139 _7946 _7947 _7948) (Peano.lt _7946 _7948)). Qed.
Lemma lem367014 (a : Prop) (b : Prop) : (term241 a b) = (term242 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem367015 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term243 _7946 _7947 _7948) = (term244 _7946 _7947 _7948).
Proof. exact (@lem367014 (term216 _7946 _7947) (term65 _7947 _7948)). Qed.
Lemma lem367017 (a : Prop) : (term245 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem367018 (_7946 : nat) (_7947 : nat) : (term246 _7946 _7947) = (Peano.lt _7946 _7947).
Proof. exact (@lem367017 (Peano.lt _7946 _7947)). Qed.
Lemma lem367019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem367020 (_7946 : nat) (_7947 : nat) : (term247 _7946 _7947) = (term248 _7946 _7947).
Proof. exact (MK_COMB (@lem367019) (@lem367018 _7946 _7947)). Qed.
Lemma lem367022 (a : Prop) : (term245 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem367023 (_7947 : nat) (_7948 : nat) : (term151 _7947 _7948) = (Peano.le _7947 _7948).
Proof. exact (@lem367022 (Peano.le _7947 _7948)). Qed.
Lemma lem367024 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term244 _7946 _7947 _7948) = (term144 _7946 _7947 _7948).
Proof. exact (MK_COMB (@lem367020 _7946 _7947) (@lem367023 _7947 _7948)). Qed.
Lemma lem367025 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term243 _7946 _7947 _7948) = (term144 _7946 _7947 _7948).
Proof. exact (TRANS (@lem367015 _7946 _7947 _7948) (@lem367024 _7946 _7947 _7948)). Qed.
Lemma lem367026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem367027 (_7946 : nat) (_7947 : nat) (_7948 : nat) : (term249 _7946 _7947 _7948) = (term250 _7946 _7947 _7948).
Proof. exact (MK_COMB (@lem367026) (@lem367025 _7946 _7947 _7948)). Qed.
Lemma lem367028 (_7946 : nat) (_7948 : nat) : (Peano.lt _7946 _7948) = (Peano.lt _7946 _7948).
Proof. exact (eq_refl (Peano.lt _7946 _7948)). Qed.
Lemma lem367029 (_7947 : nat) (_7946 : nat) (_7948 : nat) : (term240 _7947 _7946 _7948) = (term69 _7947 _7946 _7948).
Proof. exact (MK_COMB (@lem367027 _7946 _7947 _7948) (@lem367028 _7946 _7948)). Qed.
Lemma lem367030 (_7947 : nat) (_7946 : nat) (_7948 : nat) : (term237 _7946 _7947 _7948) = (term69 _7947 _7946 _7948).
Proof. exact (TRANS (@lem367012 _7947 _7946 _7948) (@lem367029 _7947 _7946 _7948)). Qed.
Lemma lem367032 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term251 _16436 y a m b.
Proof. exact (conj (@lem366930 _16436 y a m b h1) (@lem366937 _16436 y a m b h1)). Qed.
Lemma lem367034 (_7947 : nat) (_7946 : nat) (_7948 : nat) (h1 : term75) : term69 _7947 _7946 _7948.
Proof. exact (EQ_MP (@lem367030 _7947 _7946 _7948) (@lem367009 _7946 _7947 _7948 h1)). Qed.
Lemma lem367035 {_16436 : Type'} (a : _16436) (y : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) : term252 _16436 a y m b.
Proof. exact (@lem367034 (m a) (m y) (m b) h1). Qed.
Lemma lem367038 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : term20 _16436 y m b.
Proof. exact (@lem367035 _16436 a y m b h1 (@lem367032 _16436 y a m b h2)). Qed.
Lemma lem367039 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : term232 _16436 y m b.
Proof. exact (fun h0 : term217 _16436 y m b => @lem367038 _16436 y a m b h1 h2). Qed.
Lemma lem367041 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem367042 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term232 _16436 y m b) = (term20 _16436 y m b).
Proof. exact (@lem367041 (term20 _16436 y m b)). Qed.
Lemma lem367043 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : term20 _16436 y m b.
Proof. exact (EQ_MP (@lem367042 _16436 y m b) (@lem367039 _16436 y a m b h1 h2)). Qed.
Lemma lem367046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem367048 {_16436 : Type'} (y : _16436) (m : _16436 -> nat) (b : _16436) : (term217 _16436 y m b) = (term253 _16436 y m b).
Proof. exact (@lem367046 (term20 _16436 y m b)). Qed.
Lemma lem367051 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term119 _16436 y a m b) : term253 _16436 y m b.
Proof. exact (EQ_MP (@lem367048 _16436 y m b) (@lem366864 _16436 y a m b h1)). Qed.
Lemma lem367054 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : False.
Proof. exact (@lem367051 _16436 y a m b h2 (@lem367043 _16436 y a m b h1 h2)). Qed.
Lemma lem367055 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : term231.
Proof. exact (fun h0 : ~ False => @lem367054 _16436 y a m b h1 h2). Qed.
Lemma lem367057 (p : Prop) : (term229 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem367058 : term231 = False.
Proof. exact (@lem367057 False). Qed.
Lemma lem367059 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term119 _16436 y a m b) : False.
Proof. exact (EQ_MP (@lem367058) (@lem367055 _16436 y a m b h1 h2)). Qed.
Lemma lem367060 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : term78 = False.
Proof. exact (prop_ext (fun h4 : term78 => @lem366923 _16436 a m b h1 h2 h3) (fun h4 : False => @lem366597 h2)). Qed.
Lemma lem367061 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term44) (h2 : term78) (h3 : term101 _16436 a m b) : False.
Proof. exact (EQ_MP (@lem367060 _16436 a m b h1 h2 h3) (@lem366597 h2)). Qed.
Lemma lem367062 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term134 _16436 y a m b) : False.
Proof. exact (or_elim (@lem366580 _16436 y a m b h4) (fun h0 : term101 _16436 a m b => @lem367061 _16436 a m b h2 h3 h0) (fun h0 : term119 _16436 y a m b => @lem367059 _16436 y a m b h1 h0)). Qed.
Lemma lem367063 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term134 _16436 y a m b) : (term134 _16436 y a m b) = False.
Proof. exact (prop_ext (fun h5 : term134 _16436 y a m b => @lem367062 _16436 y a m b h1 h2 h3 h4) (fun h5 : False => @lem366580 _16436 y a m b h4)). Qed.
Lemma lem367064 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term134 _16436 y a m b) : False.
Proof. exact (EQ_MP (@lem367063 _16436 y a m b h1 h2 h3 h4) (@lem366580 _16436 y a m b h4)). Qed.
Lemma lem367065 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term134 _16436 y a m b) : term78 = False.
Proof. exact (prop_ext (fun h5 : term78 => @lem367064 _16436 y a m b h1 h2 h3 h4) (fun h5 : False => @lem366420 h3)). Qed.
Lemma lem367066 {_16436 : Type'} (y : _16436) (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term134 _16436 y a m b) : False.
Proof. exact (EQ_MP (@lem367065 _16436 y a m b h1 h2 h3 h4) (@lem366420 h3)). Qed.
Lemma lem367067 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term37 _16436 a m b) : False.
Proof. exact (ex_elim (@lem366023 _16436 a m b h4) (fun y : _16436 => fun h0 : term136 _16436 a m b y => @lem367066 _16436 y a m b h1 h2 h3 h0)). Qed.
Lemma lem367068 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term37 _16436 a m b) : term78 = False.
Proof. exact (prop_ext (fun h5 : term78 => @lem367067 _16436 a m b h1 h2 h3 h4) (fun h5 : False => @lem366036 h3)). Qed.
Lemma lem367069 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term44) (h3 : term78) (h4 : term37 _16436 a m b) : False.
Proof. exact (EQ_MP (@lem367068 _16436 a m b h1 h2 h3 h4) (@lem366036 h3)). Qed.
Lemma lem367070 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term78) (h3 : term37 _16436 a m b) : term42.
Proof. exact (fun h0 : term44 => @lem367069 _16436 a m b h1 h0 h2 h3). Qed.
Lemma lem367071 : term42 = term43.
Proof. exact (@lem69 term44). Qed.
Lemma lem367072 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term75) (h2 : term78) (h3 : term37 _16436 a m b) : term43.
Proof. exact (EQ_MP (@lem367071) (@lem367070 _16436 a m b h1 h2 h3)). Qed.
Lemma lem367073 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term78) (h2 : term37 _16436 a m b) : term47.
Proof. exact (fun h0 : term75 => @lem367072 _16436 a m b h0 h1 h2). Qed.
Lemma lem367074 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term50.
Proof. exact (fun h0 : term78 => @lem367073 _16436 a m b h0 h1). Qed.
Lemma lem367075 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term52 _16436 a m b.
Proof. exact (fun h0 : term37 _16436 a m b => @lem367074 _16436 a m b h0). Qed.
Lemma lem367080 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : term56 _16436 m b.
Proof. exact (fun a : _16436 => @lem367075 _16436 a m b). Qed.
Lemma lem367085 {_16436 : Type'} (b : _16436) : term60 _16436 b.
Proof. exact (fun m : _16436 -> nat => @lem367080 _16436 m b). Qed.
Lemma lem367090 {_16436 : Type'} : term64 _16436.
Proof. exact (fun b : _16436 => @lem367085 _16436 b). Qed.
Lemma lem367091 {_16436 : Type'} : term63 _16436.
Proof. exact (EQ_MP (@lem365832 _16436) (@lem367090 _16436)). Qed.
Lemma lem367092 {_16436 : Type'} (b : _16436) : term254 _16436 b.
Proof. exact (@lem367091 _16436 b). Qed.
Lemma lem367093 {_16436 : Type'} (b : _16436) : (term254 _16436 b) = (term59 _16436 b).
Proof. exact (eq_refl (term254 _16436 b)). Qed.
Lemma lem367094 {_16436 : Type'} (b : _16436) : term59 _16436 b.
Proof. exact (EQ_MP (@lem367093 _16436 b) (@lem367092 _16436 b)). Qed.
Lemma lem367095 {_16436 : Type'} (b : _16436) (m : _16436 -> nat) : term255 _16436 b m.
Proof. exact (@lem367094 _16436 b m). Qed.
Lemma lem367096 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : (term255 _16436 b m) = (term55 _16436 m b).
Proof. exact (eq_refl (term255 _16436 b m)). Qed.
Lemma lem367097 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) : term55 _16436 m b.
Proof. exact (EQ_MP (@lem367096 _16436 m b) (@lem367095 _16436 b m)). Qed.
Lemma lem367098 {_16436 : Type'} (m : _16436 -> nat) (b : _16436) (a : _16436) : term256 _16436 m b a.
Proof. exact (@lem367097 _16436 m b a). Qed.
Lemma lem367099 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term256 _16436 m b a) = (term38 _16436 a m b).
Proof. exact (eq_refl (term256 _16436 m b a)). Qed.
Lemma lem367100 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term38 _16436 a m b.
Proof. exact (EQ_MP (@lem367099 _16436 a m b) (@lem367098 _16436 m b a)). Qed.
Lemma lem367102 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term38 _16436 a m b.
Proof. exact (@lem365593 _16436 a m b (@lem367100 _16436 a m b)). Qed.
Lemma lem367103 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term49.
Proof. exact (@lem367102 _16436 a m b (@lem365577 _16436 a m b h1)). Qed.
Lemma lem367104 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term46.
Proof. exact (@lem367103 _16436 a m b h1 (@lem91686)). Qed.
Lemma lem367105 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : term42.
Proof. exact (@lem367104 _16436 a m b h1 (@lem95941)). Qed.
Lemma lem367106 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : False.
Proof. exact (@lem367105 _16436 a m b h1 (@lem97961)). Qed.
Lemma lem367107 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : (term37 _16436 a m b) = False.
Proof. exact (prop_ext (fun h2 : term37 _16436 a m b => @lem367106 _16436 a m b h1) (fun h2 : False => @lem365577 _16436 a m b h1)). Qed.
Lemma lem367108 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) (h1 : term37 _16436 a m b) : False.
Proof. exact (EQ_MP (@lem367107 _16436 a m b h1) (@lem365577 _16436 a m b h1)). Qed.
Lemma lem367109 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : term36 _16436 a m b.
Proof. exact (fun h0 : term37 _16436 a m b => @lem367108 _16436 a m b h0). Qed.
Lemma lem367110 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term31 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (EQ_MP (@lem365576 _16436 a m b) (@lem367109 _16436 a m b)). Qed.
Lemma lem367111 {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436) : (term30 _16436 a m b) = (term34 _16436 a m b).
Proof. exact (EQ_MP (@lem365572 _16436 a m b) (@lem367110 _16436 a m b)). Qed.
