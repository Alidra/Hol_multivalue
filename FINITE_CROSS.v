Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CROSS_term_abbrevs.
Require Import CROSS_spec.
Require Import FINITE_PRODUCT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4325463 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4323391 A B s). Qed.
Lemma lem4325464 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4325465 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4325464 A B s) (@lem4325463 A B s)). Qed.
Lemma lem4325466 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem4325465 A B s t). Qed.
Lemma lem4325467 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term2 A B s t) = (term3 A B s t).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem4325468 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (EQ_MP (@lem4325467 A B s t) (@lem4325466 A B s t)). Qed.
Lemma lem4325469 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term4 A B s t.
Proof. exact (h1). Qed.
Lemma lem4325470 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : term5 A B s t.
Proof. exact (@lem4325468 A B s t (@lem4325469 A B s t h1)). Qed.
Lemma lem4325471 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term5 A B s t) = ((term5 A B s t) = True).
Proof. exact (@lem7 (term5 A B s t)). Qed.
Lemma lem4325472 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B s t) : (term5 A B s t) = True.
Proof. exact (EQ_MP (@lem4325471 A B s t) (@lem4325470 A B s t h1)). Qed.
Lemma lem4325478 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term6 _103681 _103682 s.
Proof. exact (@lem4325236 _103681 _103682 s). Qed.
Lemma lem4325479 {_103681 _103682 : Type'} (s : _103682 -> Prop) : (term6 _103681 _103682 s) = (term7 _103681 _103682 s).
Proof. exact (eq_refl (term6 _103681 _103682 s)). Qed.
Lemma lem4325480 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term7 _103681 _103682 s.
Proof. exact (EQ_MP (@lem4325479 _103681 _103682 s) (@lem4325478 _103681 _103682 s)). Qed.
Lemma lem4325481 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : term8 _103681 _103682 s t.
Proof. exact (@lem4325480 _103681 _103682 s t). Qed.
Lemma lem4325482 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (term8 _103681 _103682 s t) = ((@CROSS _103681 _103682 s t) = (term9 _103681 _103682 s t)).
Proof. exact (eq_refl (term8 _103681 _103682 s t)). Qed.
Lemma lem4325495 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term10 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4325496 (p : Prop) (q : Prop) (p' : Prop) : term11 p q p'.
Proof. exact (fun q' : Prop => @lem4325495 p q p' q'). Qed.
Lemma lem4325497 (p : Prop) (q : Prop) : term12 p q.
Proof. exact (fun p' : Prop => @lem4325496 p q p'). Qed.
Lemma lem4325498 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term13 _103774 _103776 s t.
Proof. exact (@lem4325497 (term4 _103774 _103776 s t) (term14 _103774 _103776 s t)). Qed.
Lemma lem4325499 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) : term15 _103774 _103776 s t p'.
Proof. exact (@lem4325498 _103774 _103776 s t p'). Qed.
Lemma lem4325500 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) : (term15 _103774 _103776 s t p') = (term16 _103774 _103776 s t p').
Proof. exact (eq_refl (term15 _103774 _103776 s t p')). Qed.
Lemma lem4325501 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) : term16 _103774 _103776 s t p'.
Proof. exact (EQ_MP (@lem4325500 _103774 _103776 s t p') (@lem4325499 _103774 _103776 s t p')). Qed.
Lemma lem4325502 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) (q' : Prop) : term17 _103774 _103776 s t p' q'.
Proof. exact (@lem4325501 _103774 _103776 s t p' q'). Qed.
Lemma lem4325503 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) (q' : Prop) : (term17 _103774 _103776 s t p' q') = (term18 _103774 _103776 s t p' q').
Proof. exact (eq_refl (term17 _103774 _103776 s t p' q')). Qed.
Lemma lem4325504 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (p' : Prop) (q' : Prop) : term18 _103774 _103776 s t p' q'.
Proof. exact (EQ_MP (@lem4325503 _103774 _103776 s t p' q') (@lem4325502 _103774 _103776 s t p' q')). Qed.
Lemma lem4325507 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term4 _103774 _103776 s t) = (term4 _103774 _103776 s t).
Proof. exact (eq_refl (term4 _103774 _103776 s t)). Qed.
Lemma lem4325508 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (q' : Prop) : term19 _103774 _103776 s t q'.
Proof. exact (@lem4325504 _103774 _103776 s t (term4 _103774 _103776 s t) q'). Qed.
Lemma lem4325509 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (q' : Prop) : term20 _103774 _103776 s t q'.
Proof. exact (@lem4325508 _103774 _103776 s t q' (@lem4325507 _103774 _103776 s t)). Qed.
Lemma lem4325510 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : term4 _103774 _103776 s t.
Proof. exact (h1). Qed.
Lemma lem4325511 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : @FINITE _103776 t.
Proof. exact (proj2 (@lem4325510 _103774 _103776 s t h1)). Qed.
Lemma lem4325512 {_103776 : Type'} (t : _103776 -> Prop) : (@FINITE _103776 t) = ((@FINITE _103776 t) = True).
Proof. exact (@lem7 (@FINITE _103776 t)). Qed.
Lemma lem4325514 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : @FINITE _103774 s.
Proof. exact (proj1 (@lem4325510 _103774 _103776 s t h1)). Qed.
Lemma lem4325515 {_103774 : Type'} (s : _103774 -> Prop) : (@FINITE _103774 s) = ((@FINITE _103774 s) = True).
Proof. exact (@lem7 (@FINITE _103774 s)). Qed.
Lemma lem4325518 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (@CROSS _103681 _103682 s t) = (term9 _103681 _103682 s t).
Proof. exact (EQ_MP (@lem4325482 _103681 _103682 s t) (@lem4325481 _103681 _103682 s t)). Qed.
Lemma lem4325519 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (@CROSS _103776 _103774 s t) = (term21 _103774 _103776 s t).
Proof. exact (@lem4325518 _103776 _103774 s t). Qed.
Lemma lem4325530 {_103774 _103776 : Type'} : (@FINITE (prod _103774 _103776)) = (@FINITE (prod _103774 _103776)).
Proof. exact (eq_refl (@FINITE (prod _103774 _103776))). Qed.
Lemma lem4325531 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term14 _103774 _103776 s t) = (term5 _103774 _103776 s t).
Proof. exact (MK_COMB (@lem4325530 _103774 _103776) (@lem4325519 _103774 _103776 s t)). Qed.
Lemma lem4325533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term22 A B s t.
Proof. exact (fun h0 : term4 A B s t => @lem4325472 A B s t h0). Qed.
Lemma lem4325534 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term22 _103774 _103776 s t.
Proof. exact (@lem4325533 _103774 _103776 s t). Qed.
Lemma lem4325538 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (@FINITE _103774 s) = True.
Proof. exact (EQ_MP (@lem4325515 _103774 s) (@lem4325514 _103774 _103776 s t h1)). Qed.
Lemma lem4325539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4325540 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (term23 _103774 s) = (and True).
Proof. exact (MK_COMB (@lem4325539) (@lem4325538 _103774 _103776 s t h1)). Qed.
Lemma lem4325542 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (@FINITE _103776 t) = True.
Proof. exact (EQ_MP (@lem4325512 _103776 t) (@lem4325511 _103774 _103776 s t h1)). Qed.
Lemma lem4325543 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (term4 _103774 _103776 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4325540 _103774 _103776 s t h1) (@lem4325542 _103774 _103776 s t h1)). Qed.
Lemma lem4325545 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4325546 : (True /\ True) = True.
Proof. exact (@lem4325545 True). Qed.
Lemma lem4325547 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (term4 _103774 _103776 s t) = True.
Proof. exact (TRANS (@lem4325543 _103774 _103776 s t h1) (@lem4325546)). Qed.
Lemma lem4325548 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : True = (term4 _103774 _103776 s t).
Proof. exact (SYM (@lem4325547 _103774 _103776 s t h1)). Qed.
Lemma lem4325549 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : term4 _103774 _103776 s t.
Proof. exact (EQ_MP (@lem4325548 _103774 _103776 s t h1) (@lem0)). Qed.
Lemma lem4325550 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (term5 _103774 _103776 s t) = True.
Proof. exact (@lem4325534 _103774 _103776 s t (@lem4325549 _103774 _103776 s t h1)). Qed.
Lemma lem4325551 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) (h1 : term4 _103774 _103776 s t) : (term14 _103774 _103776 s t) = True.
Proof. exact (TRANS (@lem4325531 _103774 _103776 s t) (@lem4325550 _103774 _103776 s t h1)). Qed.
Lemma lem4325552 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term24 _103774 _103776 s t.
Proof. exact (fun h0 : term4 _103774 _103776 s t => @lem4325551 _103774 _103776 s t h0). Qed.
Lemma lem4325553 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : term25 _103774 _103776 s t.
Proof. exact (@lem4325509 _103774 _103776 s t True). Qed.
Lemma lem4325554 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term26 _103774 _103776 s t) = (term27 _103774 _103776 s t).
Proof. exact (@lem4325553 _103774 _103776 s t (@lem4325552 _103774 _103776 s t)). Qed.
Lemma lem4325556 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4325557 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term27 _103774 _103776 s t) = True.
Proof. exact (@lem4325556 (term4 _103774 _103776 s t)). Qed.
Lemma lem4325558 {_103774 _103776 : Type'} (s : _103774 -> Prop) (t : _103776 -> Prop) : (term26 _103774 _103776 s t) = True.
Proof. exact (TRANS (@lem4325554 _103774 _103776 s t) (@lem4325557 _103774 _103776 s t)). Qed.
Lemma lem4325559 {_103774 _103776 : Type'} (s : _103774 -> Prop) : (term28 _103774 _103776 s) = (term29 _103776).
Proof. exact (fun_ext (fun t : _103776 -> Prop => @lem4325558 _103774 _103776 s t)). Qed.
Lemma lem4325560 {_103776 : Type'} : (@all (_103776 -> Prop)) = (@all (_103776 -> Prop)).
Proof. exact (eq_refl (@all (_103776 -> Prop))). Qed.
Lemma lem4325561 {_103774 _103776 : Type'} (s : _103774 -> Prop) : (term30 _103774 _103776 s) = (term31 _103776).
Proof. exact (MK_COMB (@lem4325560 _103776) (@lem4325559 _103774 _103776 s)). Qed.
Lemma lem4325563 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325564 {_103776 : Type'} (t : Prop) : (term33 _103776 t) = t.
Proof. exact (@lem4325563 (_103776 -> Prop) t). Qed.
Lemma lem4325565 {_103776 : Type'} : (term31 _103776) = True.
Proof. exact (@lem4325564 _103776 True). Qed.
Lemma lem4325566 {_103774 _103776 : Type'} (s : _103774 -> Prop) : (term30 _103774 _103776 s) = True.
Proof. exact (TRANS (@lem4325561 _103774 _103776 s) (@lem4325565 _103776)). Qed.
Lemma lem4325567 {_103774 _103776 : Type'} : (term34 _103774 _103776) = (term29 _103774).
Proof. exact (fun_ext (fun s : _103774 -> Prop => @lem4325566 _103774 _103776 s)). Qed.
Lemma lem4325568 {_103774 : Type'} : (@all (_103774 -> Prop)) = (@all (_103774 -> Prop)).
Proof. exact (eq_refl (@all (_103774 -> Prop))). Qed.
Lemma lem4325569 {_103774 _103776 : Type'} : (term35 _103774 _103776) = (term31 _103774).
Proof. exact (MK_COMB (@lem4325568 _103774) (@lem4325567 _103774 _103776)). Qed.
Lemma lem4325571 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325572 {_103774 : Type'} (t : Prop) : (term33 _103774 t) = t.
Proof. exact (@lem4325571 (_103774 -> Prop) t). Qed.
Lemma lem4325573 {_103774 : Type'} : (term31 _103774) = True.
Proof. exact (@lem4325572 _103774 True). Qed.
Lemma lem4325574 {_103774 _103776 : Type'} : (term35 _103774 _103776) = True.
Proof. exact (TRANS (@lem4325569 _103774 _103776) (@lem4325573 _103774)). Qed.
Lemma lem4325575 {_103774 _103776 : Type'} : True = (term35 _103774 _103776).
Proof. exact (SYM (@lem4325574 _103774 _103776)). Qed.
Lemma lem4325576 {_103774 _103776 : Type'} : term35 _103774 _103776.
Proof. exact (EQ_MP (@lem4325575 _103774 _103776) (@lem0)). Qed.
