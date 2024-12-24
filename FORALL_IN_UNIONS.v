Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Lemma lem3325376 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3325377 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3325378 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3325377 t1) (@lem3325376 t1)). Qed.
Lemma lem3325379 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3325378 t1 t2). Qed.
Lemma lem3325380 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3325381 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3325380 t1 t2) (@lem3325379 t1 t2)). Qed.
Lemma lem3325382 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3325381 t1 t2 t3). Qed.
Lemma lem3325383 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3325384 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3325383 t1 t2 t3) (@lem3325382 t1 t2 t3)). Qed.
Lemma lem3325385 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3325384 t1 t2 t3)). Qed.
Lemma lem3325435 {A : Type'} (s : type686 A) (x : A) : (term7 A x s) = (term8 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3325436 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term7 _86883 x s) = (term8 _86883 s x).
Proof. exact (@lem3325435 _86883 s x). Qed.
Lemma lem3325444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3325445 {_86883 : Type'} (P : type686 _86883) (x : _86883 -> Prop) : (@IN (_86883 -> Prop) x P) = (P x).
Proof. exact (@lem3325444 (_86883 -> Prop) P x). Qed.
Lemma lem3325446 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (@IN (_86883 -> Prop) t s) = (s t).
Proof. exact (@lem3325445 _86883 s t). Qed.
Lemma lem3325447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3325448 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term9 _86883 t s) = (term10 _86883 s t).
Proof. exact (MK_COMB (@lem3325447) (@lem3325446 _86883 s t)). Qed.
Lemma lem3325450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3325451 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (@IN _86883 x P) = (P x).
Proof. exact (@lem3325450 _86883 P x). Qed.
Lemma lem3325452 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (@IN _86883 x t) = (t x).
Proof. exact (@lem3325451 _86883 t x). Qed.
Lemma lem3325453 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term11 _86883 s x t) = (term12 _86883 s t x).
Proof. exact (MK_COMB (@lem3325448 _86883 s t) (@lem3325452 _86883 t x)). Qed.
Lemma lem3325456 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term13 _86883 s x) = (term14 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325453 _86883 s t x)). Qed.
Lemma lem3325457 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3325458 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term8 _86883 s x) = (term15 _86883 s x).
Proof. exact (MK_COMB (@lem3325457 _86883) (@lem3325456 _86883 s x)). Qed.
Lemma lem3325463 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term7 _86883 x s) = (term15 _86883 s x).
Proof. exact (TRANS (@lem3325436 _86883 s x) (@lem3325458 _86883 s x)). Qed.
Lemma lem3325464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3325465 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term16 _86883 x s) = (term17 _86883 s x).
Proof. exact (MK_COMB (@lem3325464) (@lem3325463 _86883 s x)). Qed.
Lemma lem3325466 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3325467 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term18 _86883 s P x) = (term19 _86883 s P x).
Proof. exact (MK_COMB (@lem3325465 _86883 s x) (@lem3325466 _86883 P x)). Qed.
Lemma lem3325470 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term20 _86883 s P) = (term21 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325467 _86883 s P x)). Qed.
Lemma lem3325471 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325472 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term22 _86883 s P) = (term23 _86883 s P).
Proof. exact (MK_COMB (@lem3325471 _86883) (@lem3325470 _86883 s P)). Qed.
Lemma lem3325477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3325478 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term24 _86883 s P) = (term25 _86883 s P).
Proof. exact (MK_COMB (@lem3325477) (@lem3325472 _86883 s P)). Qed.
Lemma lem3325492 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3325493 {_86883 : Type'} (P : type686 _86883) (x : _86883 -> Prop) : (@IN (_86883 -> Prop) x P) = (P x).
Proof. exact (@lem3325492 (_86883 -> Prop) P x). Qed.
Lemma lem3325494 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (@IN (_86883 -> Prop) t s) = (s t).
Proof. exact (@lem3325493 _86883 s t). Qed.
Lemma lem3325495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3325496 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term9 _86883 t s) = (term10 _86883 s t).
Proof. exact (MK_COMB (@lem3325495) (@lem3325494 _86883 s t)). Qed.
Lemma lem3325498 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3325499 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (@IN _86883 x P) = (P x).
Proof. exact (@lem3325498 _86883 P x). Qed.
Lemma lem3325500 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (@IN _86883 x t) = (t x).
Proof. exact (@lem3325499 _86883 t x). Qed.
Lemma lem3325501 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term11 _86883 s x t) = (term12 _86883 s t x).
Proof. exact (MK_COMB (@lem3325496 _86883 s t) (@lem3325500 _86883 t x)). Qed.
Lemma lem3325504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3325505 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term26 _86883 s x t) = (term27 _86883 s t x).
Proof. exact (MK_COMB (@lem3325504) (@lem3325501 _86883 s t x)). Qed.
Lemma lem3325506 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3325507 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term28 _86883 s t P x) = (term29 _86883 s t P x).
Proof. exact (MK_COMB (@lem3325505 _86883 s t x) (@lem3325506 _86883 P x)). Qed.
Lemma lem3325510 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term30 _86883 s t P) = (term31 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325507 _86883 s t P x)). Qed.
Lemma lem3325511 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325512 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term32 _86883 s t P) = (term33 _86883 s t P).
Proof. exact (MK_COMB (@lem3325511 _86883) (@lem3325510 _86883 s t P)). Qed.
Lemma lem3325517 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term34 _86883 s P) = (term35 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325512 _86883 s t P)). Qed.
Lemma lem3325518 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325519 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term36 _86883 s P) = (term37 _86883 s P).
Proof. exact (MK_COMB (@lem3325518 _86883) (@lem3325517 _86883 s P)). Qed.
Lemma lem3325524 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term22 _86883 s P) = (term36 _86883 s P)) = ((term23 _86883 s P) = (term37 _86883 s P)).
Proof. exact (MK_COMB (@lem3325478 _86883 s P) (@lem3325519 _86883 s P)). Qed.
Lemma lem3325527 {_86883 : Type'} (P : _86883 -> Prop) : (term38 _86883 P) = (term39 _86883 P).
Proof. exact (fun_ext (fun s : type686 _86883 => @lem3325524 _86883 s P)). Qed.
Lemma lem3325528 {_86883 : Type'} : (@all ((_86883 -> Prop) -> Prop)) = (@all ((_86883 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86883 -> Prop) -> Prop))). Qed.
Lemma lem3325529 {_86883 : Type'} (P : _86883 -> Prop) : (term40 _86883 P) = (term41 _86883 P).
Proof. exact (MK_COMB (@lem3325528 _86883) (@lem3325527 _86883 P)). Qed.
Lemma lem3325534 {_86883 : Type'} : (term42 _86883) = (term43 _86883).
Proof. exact (fun_ext (fun P : _86883 -> Prop => @lem3325529 _86883 P)). Qed.
Lemma lem3325535 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325536 {_86883 : Type'} : (term44 _86883) = (term45 _86883).
Proof. exact (MK_COMB (@lem3325535 _86883) (@lem3325534 _86883)). Qed.
Lemma lem3325541 {_86883 : Type'} : (term45 _86883) = (term44 _86883).
Proof. exact (SYM (@lem3325536 _86883)). Qed.
Lemma lem3325543 (p : Prop) : p = (term46 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3325544 {_86883 : Type'} : (term45 _86883) = (term47 _86883).
Proof. exact (@lem3325543 (term45 _86883)). Qed.
Lemma lem3325545 {_86883 : Type'} : (term47 _86883) = (term45 _86883).
Proof. exact (SYM (@lem3325544 _86883)). Qed.
Lemma lem3325546 {_86883 : Type'} (h1 : term48 _86883) : term48 _86883.
Proof. exact (h1). Qed.
Lemma lem3325549 {_86883 : Type'} (h1 : term47 _86883) : term47 _86883.
Proof. exact (h1). Qed.
Lemma lem3325550 {_86883 : Type'} : term49 _86883.
Proof. exact (fun h0 : term47 _86883 => @lem3325549 _86883 h0). Qed.
Lemma lem3325551 {_86883 : Type'} (h1 : term49 _86883) : term49 _86883.
Proof. exact (h1). Qed.
Lemma lem3325552 {_86883 : Type'} (h1 : term47 _86883) : term47 _86883.
Proof. exact (h1). Qed.
Lemma lem3325553 {_86883 : Type'} (h1 : term47 _86883) (h2 : term49 _86883) : term47 _86883.
Proof. exact (@lem3325551 _86883 h2 (@lem3325552 _86883 h1)). Qed.
Lemma lem3325554 {_86883 : Type'} (h1 : term47 _86883) : term50 _86883.
Proof. exact (fun h0 : term49 _86883 => @lem3325553 _86883 h1 h0). Qed.
Lemma lem3325555 {_86883 : Type'} (h1 : term49 _86883) : term49 _86883.
Proof. exact (h1). Qed.
Lemma lem3325556 {_86883 : Type'} (h1 : term47 _86883) (h2 : term49 _86883) : term47 _86883.
Proof. exact (@lem3325554 _86883 h1 (@lem3325555 _86883 h2)). Qed.
Lemma lem3325557 {_86883 : Type'} (h1 : term49 _86883) : term49 _86883.
Proof. exact (fun h0 : term47 _86883 => @lem3325556 _86883 h0 h1). Qed.
Lemma lem3325558 {_86883 : Type'} : term51 _86883.
Proof. exact (fun h0 : term49 _86883 => @lem3325557 _86883 h0). Qed.
Lemma lem3325561 {_86883 : Type'} : term49 _86883.
Proof. exact (@lem3325558 _86883 (@lem3325550 _86883)). Qed.
Lemma lem3325562 {_86883 : Type'} : term49 _86883.
Proof. exact (@lem3325561 _86883). Qed.
Lemma lem3325564 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3325565 {_86883 : Type'} : (term47 _86883) = (term52 _86883).
Proof. exact (@lem3325564 (term48 _86883)). Qed.
Lemma lem3325567 (t : Prop) : (term53 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3325568 {_86883 : Type'} : (term52 _86883) = (term45 _86883).
Proof. exact (@lem3325567 (term45 _86883)). Qed.
Lemma lem3325629 {_86883 : Type'} : (term47 _86883) = (term45 _86883).
Proof. exact (TRANS (@lem3325565 _86883) (@lem3325568 _86883)). Qed.
Lemma lem3325638 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term29 _86883 s t P x) = (term29 _86883 s t P x).
Proof. exact (eq_refl (term29 _86883 s t P x)). Qed.
Lemma lem3325639 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term31 _86883 s t P) = (term31 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325638 _86883 s t P x)). Qed.
Lemma lem3325640 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325641 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term33 _86883 s t P) = (term33 _86883 s t P).
Proof. exact (MK_COMB (@lem3325640 _86883) (@lem3325639 _86883 s t P)). Qed.
Lemma lem3325642 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term35 _86883 s P) = (term35 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325641 _86883 s t P)). Qed.
Lemma lem3325643 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325644 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term37 _86883 s P) = (term37 _86883 s P).
Proof. exact (MK_COMB (@lem3325643 _86883) (@lem3325642 _86883 s P)). Qed.
Lemma lem3325645 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3325650 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term12 _86883 s t x) = (term12 _86883 s t x).
Proof. exact (eq_refl (term12 _86883 s t x)). Qed.
Lemma lem3325651 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term14 _86883 s x) = (term14 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325650 _86883 s t x)). Qed.
Lemma lem3325652 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3325653 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term15 _86883 s x) = (term15 _86883 s x).
Proof. exact (MK_COMB (@lem3325652 _86883) (@lem3325651 _86883 s x)). Qed.
Lemma lem3325654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3325655 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term17 _86883 s x) = (term17 _86883 s x).
Proof. exact (MK_COMB (@lem3325654) (@lem3325653 _86883 s x)). Qed.
Lemma lem3325656 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term19 _86883 s P x) = (term19 _86883 s P x).
Proof. exact (MK_COMB (@lem3325655 _86883 s x) (@lem3325645 _86883 P x)). Qed.
Lemma lem3325657 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term21 _86883 s P) = (term21 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325656 _86883 s P x)). Qed.
Lemma lem3325658 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325659 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term23 _86883 s P) = (term23 _86883 s P).
Proof. exact (MK_COMB (@lem3325658 _86883) (@lem3325657 _86883 s P)). Qed.
Lemma lem3325660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3325661 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term25 _86883 s P) = (term25 _86883 s P).
Proof. exact (MK_COMB (@lem3325660) (@lem3325659 _86883 s P)). Qed.
Lemma lem3325662 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term23 _86883 s P) = (term37 _86883 s P)) = ((term23 _86883 s P) = (term37 _86883 s P)).
Proof. exact (MK_COMB (@lem3325661 _86883 s P) (@lem3325644 _86883 s P)). Qed.
Lemma lem3325663 {_86883 : Type'} (P : _86883 -> Prop) : (term39 _86883 P) = (term39 _86883 P).
Proof. exact (fun_ext (fun s : type686 _86883 => @lem3325662 _86883 s P)). Qed.
Lemma lem3325664 {_86883 : Type'} : (@all ((_86883 -> Prop) -> Prop)) = (@all ((_86883 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86883 -> Prop) -> Prop))). Qed.
Lemma lem3325665 {_86883 : Type'} (P : _86883 -> Prop) : (term41 _86883 P) = (term41 _86883 P).
Proof. exact (MK_COMB (@lem3325664 _86883) (@lem3325663 _86883 P)). Qed.
Lemma lem3325666 {_86883 : Type'} : (term43 _86883) = (term43 _86883).
Proof. exact (fun_ext (fun P : _86883 -> Prop => @lem3325665 _86883 P)). Qed.
Lemma lem3325667 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325668 {_86883 : Type'} : (term45 _86883) = (term45 _86883).
Proof. exact (MK_COMB (@lem3325667 _86883) (@lem3325666 _86883)). Qed.
Lemma lem3325715 {_86883 : Type'} : (term47 _86883) = (term45 _86883).
Proof. exact (TRANS (@lem3325629 _86883) (@lem3325668 _86883)). Qed.
Lemma lem3325716 {_86883 : Type'} : (term45 _86883) = (term47 _86883).
Proof. exact (SYM (@lem3325715 _86883)). Qed.
Lemma lem3325718 (p : Prop) : p = (term46 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3325719 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term23 _86883 s P) = (term37 _86883 s P)) = (term54 _86883 s P).
Proof. exact (@lem3325718 ((term23 _86883 s P) = (term37 _86883 s P))). Qed.
Lemma lem3325720 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term54 _86883 s P) = ((term23 _86883 s P) = (term37 _86883 s P)).
Proof. exact (SYM (@lem3325719 _86883 s P)). Qed.
Lemma lem3325721 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (h1 : term55 _86883 s P) : term55 _86883 s P.
Proof. exact (h1). Qed.
Lemma lem3325730 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term56 _86883 s t x) = (term57 _86883 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3325733 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term12 _86883 s t x) = (term12 _86883 s t x).
Proof. exact (eq_refl (term12 _86883 s t x)). Qed.
Lemma lem3325734 {_86883 : Type'} (P : type686 _86883) : (term58 _86883 P) = (term59 _86883 P).
Proof. exact (@lem18394 (_86883 -> Prop) P). Qed.
Lemma lem3325735 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term60 _86883 s x) = (term61 _86883 s x).
Proof. exact (@lem3325734 _86883 (term14 _86883 s x)). Qed.
Lemma lem3325736 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term62 _86883 s x t) = (term12 _86883 s t x).
Proof. exact (eq_refl (term62 _86883 s x t)). Qed.
Lemma lem3325737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3325738 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term63 _86883 s x t) = (term56 _86883 s t x).
Proof. exact (MK_COMB (@lem3325737) (@lem3325736 _86883 s t x)). Qed.
Lemma lem3325739 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term63 _86883 s x t) = (term57 _86883 s t x).
Proof. exact (TRANS (@lem3325738 _86883 s t x) (@lem3325730 _86883 s t x)). Qed.
Lemma lem3325740 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term64 _86883 s x) = (term65 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325739 _86883 s t x)). Qed.
Lemma lem3325741 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325742 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term61 _86883 s x) = (term66 _86883 s x).
Proof. exact (MK_COMB (@lem3325741 _86883) (@lem3325740 _86883 s x)). Qed.
Lemma lem3325743 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term60 _86883 s x) = (term66 _86883 s x).
Proof. exact (TRANS (@lem3325735 _86883 s x) (@lem3325742 _86883 s x)). Qed.
Lemma lem3325744 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term14 _86883 s x) = (term14 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325733 _86883 s t x)). Qed.
Lemma lem3325745 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3325746 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term15 _86883 s x) = (term15 _86883 s x).
Proof. exact (MK_COMB (@lem3325745 _86883) (@lem3325744 _86883 s x)). Qed.
Lemma lem3325747 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term67 _86883 P x) = (term67 _86883 P x).
Proof. exact (eq_refl (term67 _86883 P x)). Qed.
Lemma lem3325748 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3325749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3325750 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term68 _86883 s x) = (term68 _86883 s x).
Proof. exact (MK_COMB (@lem3325749) (@lem3325746 _86883 s x)). Qed.
Lemma lem3325751 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term69 _86883 s P x) = (term69 _86883 s P x).
Proof. exact (MK_COMB (@lem3325750 _86883 s x) (@lem3325747 _86883 P x)). Qed.
Lemma lem3325752 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term70 _86883 s P x) = (term69 _86883 s P x).
Proof. exact (@lem17362 (term15 _86883 s x) (P x)). Qed.
Lemma lem3325753 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term70 _86883 s P x) = (term69 _86883 s P x).
Proof. exact (TRANS (@lem3325752 _86883 s P x) (@lem3325751 _86883 s P x)). Qed.
Lemma lem3325754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3325755 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term71 _86883 s x) = (term72 _86883 s x).
Proof. exact (MK_COMB (@lem3325754) (@lem3325743 _86883 s x)). Qed.
Lemma lem3325756 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term73 _86883 s P x) = (term74 _86883 s P x).
Proof. exact (MK_COMB (@lem3325755 _86883 s x) (@lem3325748 _86883 P x)). Qed.
Lemma lem3325757 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term19 _86883 s P x) = (term73 _86883 s P x).
Proof. exact (@lem17265 (term15 _86883 s x) (P x)). Qed.
Lemma lem3325758 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term19 _86883 s P x) = (term74 _86883 s P x).
Proof. exact (TRANS (@lem3325757 _86883 s P x) (@lem3325756 _86883 s P x)). Qed.
Lemma lem3325759 {_86883 : Type'} (P : _86883 -> Prop) : (term75 _86883 P) = (term76 _86883 P).
Proof. exact (@lem18392 _86883 P). Qed.
Lemma lem3325760 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term77 _86883 s P) = (term78 _86883 s P).
Proof. exact (@lem3325759 _86883 (term21 _86883 s P)). Qed.
Lemma lem3325761 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term79 _86883 s P x) = (term19 _86883 s P x).
Proof. exact (eq_refl (term79 _86883 s P x)). Qed.
Lemma lem3325762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3325763 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term80 _86883 s P x) = (term70 _86883 s P x).
Proof. exact (MK_COMB (@lem3325762) (@lem3325761 _86883 s P x)). Qed.
Lemma lem3325764 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term80 _86883 s P x) = (term69 _86883 s P x).
Proof. exact (TRANS (@lem3325763 _86883 s P x) (@lem3325753 _86883 s P x)). Qed.
Lemma lem3325765 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term81 _86883 s P) = (term82 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325764 _86883 s P x)). Qed.
Lemma lem3325766 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3325767 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term78 _86883 s P) = (term83 _86883 s P).
Proof. exact (MK_COMB (@lem3325766 _86883) (@lem3325765 _86883 s P)). Qed.
Lemma lem3325768 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term77 _86883 s P) = (term83 _86883 s P).
Proof. exact (TRANS (@lem3325760 _86883 s P) (@lem3325767 _86883 s P)). Qed.
Lemma lem3325769 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term21 _86883 s P) = (term84 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325758 _86883 s P x)). Qed.
Lemma lem3325770 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325771 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term23 _86883 s P) = (term85 _86883 s P).
Proof. exact (MK_COMB (@lem3325770 _86883) (@lem3325769 _86883 s P)). Qed.
Lemma lem3325780 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term56 _86883 s t x) = (term57 _86883 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3325785 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3325790 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term86 _86883 s t P x) = (term87 _86883 s t P x).
Proof. exact (@lem17362 (term12 _86883 s t x) (P x)). Qed.
Lemma lem3325791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3325792 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term88 _86883 s t x) = (term89 _86883 s t x).
Proof. exact (MK_COMB (@lem3325791) (@lem3325780 _86883 s t x)). Qed.
Lemma lem3325793 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term90 _86883 s t P x) = (term91 _86883 s t P x).
Proof. exact (MK_COMB (@lem3325792 _86883 s t x) (@lem3325785 _86883 P x)). Qed.
Lemma lem3325794 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term29 _86883 s t P x) = (term90 _86883 s t P x).
Proof. exact (@lem17265 (term12 _86883 s t x) (P x)). Qed.
Lemma lem3325795 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term29 _86883 s t P x) = (term91 _86883 s t P x).
Proof. exact (TRANS (@lem3325794 _86883 s t P x) (@lem3325793 _86883 s t P x)). Qed.
Lemma lem3325796 {_86883 : Type'} (P : _86883 -> Prop) : (term75 _86883 P) = (term76 _86883 P).
Proof. exact (@lem18392 _86883 P). Qed.
Lemma lem3325797 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term92 _86883 s t P) = (term93 _86883 s t P).
Proof. exact (@lem3325796 _86883 (term31 _86883 s t P)). Qed.
Lemma lem3325798 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term94 _86883 s t P x) = (term29 _86883 s t P x).
Proof. exact (eq_refl (term94 _86883 s t P x)). Qed.
Lemma lem3325799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3325800 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term95 _86883 s t P x) = (term86 _86883 s t P x).
Proof. exact (MK_COMB (@lem3325799) (@lem3325798 _86883 s t P x)). Qed.
Lemma lem3325801 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term95 _86883 s t P x) = (term87 _86883 s t P x).
Proof. exact (TRANS (@lem3325800 _86883 s t P x) (@lem3325790 _86883 s t P x)). Qed.
Lemma lem3325802 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term96 _86883 s t P) = (term97 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325801 _86883 s t P x)). Qed.
Lemma lem3325803 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3325804 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term93 _86883 s t P) = (term98 _86883 s t P).
Proof. exact (MK_COMB (@lem3325803 _86883) (@lem3325802 _86883 s t P)). Qed.
Lemma lem3325805 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term92 _86883 s t P) = (term98 _86883 s t P).
Proof. exact (TRANS (@lem3325797 _86883 s t P) (@lem3325804 _86883 s t P)). Qed.
Lemma lem3325806 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term31 _86883 s t P) = (term99 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3325795 _86883 s t P x)). Qed.
Lemma lem3325807 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3325808 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term33 _86883 s t P) = (term100 _86883 s t P).
Proof. exact (MK_COMB (@lem3325807 _86883) (@lem3325806 _86883 s t P)). Qed.
Lemma lem3325809 {_86883 : Type'} (P : type686 _86883) : (term101 _86883 P) = (term102 _86883 P).
Proof. exact (@lem18392 (_86883 -> Prop) P). Qed.
Lemma lem3325810 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term103 _86883 s P) = (term104 _86883 s P).
Proof. exact (@lem3325809 _86883 (term35 _86883 s P)). Qed.
Lemma lem3325811 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term105 _86883 s P t) = (term33 _86883 s t P).
Proof. exact (eq_refl (term105 _86883 s P t)). Qed.
Lemma lem3325812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3325813 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term106 _86883 s P t) = (term92 _86883 s t P).
Proof. exact (MK_COMB (@lem3325812) (@lem3325811 _86883 s t P)). Qed.
Lemma lem3325814 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term106 _86883 s P t) = (term98 _86883 s t P).
Proof. exact (TRANS (@lem3325813 _86883 s t P) (@lem3325805 _86883 s t P)). Qed.
Lemma lem3325815 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term107 _86883 s P) = (term108 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325814 _86883 s t P)). Qed.
Lemma lem3325816 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3325817 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term104 _86883 s P) = (term109 _86883 s P).
Proof. exact (MK_COMB (@lem3325816 _86883) (@lem3325815 _86883 s P)). Qed.
Lemma lem3325818 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term103 _86883 s P) = (term109 _86883 s P).
Proof. exact (TRANS (@lem3325810 _86883 s P) (@lem3325817 _86883 s P)). Qed.
Lemma lem3325819 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term35 _86883 s P) = (term110 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3325808 _86883 s t P)). Qed.
Lemma lem3325820 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3325821 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term37 _86883 s P) = (term111 _86883 s P).
Proof. exact (MK_COMB (@lem3325820 _86883) (@lem3325819 _86883 s P)). Qed.
Lemma lem3325822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3325823 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term112 _86883 s P) = (term113 _86883 s P).
Proof. exact (MK_COMB (@lem3325822) (@lem3325768 _86883 s P)). Qed.
Lemma lem3325824 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term114 _86883 s P) = (term115 _86883 s P).
Proof. exact (MK_COMB (@lem3325823 _86883 s P) (@lem3325821 _86883 s P)). Qed.
Lemma lem3325825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3325826 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term116 _86883 s P) = (term117 _86883 s P).
Proof. exact (MK_COMB (@lem3325825) (@lem3325771 _86883 s P)). Qed.
Lemma lem3325827 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term118 _86883 s P) = (term119 _86883 s P).
Proof. exact (MK_COMB (@lem3325826 _86883 s P) (@lem3325818 _86883 s P)). Qed.
Lemma lem3325828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3325829 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term120 _86883 s P) = (term121 _86883 s P).
Proof. exact (MK_COMB (@lem3325828) (@lem3325827 _86883 s P)). Qed.
Lemma lem3325830 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term122 _86883 s P) = (term123 _86883 s P).
Proof. exact (MK_COMB (@lem3325829 _86883 s P) (@lem3325824 _86883 s P)). Qed.
Lemma lem3325831 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term55 _86883 s P) = (term122 _86883 s P).
Proof. exact (@lem17646 (term23 _86883 s P) (term37 _86883 s P)). Qed.
Lemma lem3325832 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term55 _86883 s P) = (term123 _86883 s P).
Proof. exact (TRANS (@lem3325831 _86883 s P) (@lem3325830 _86883 s P)). Qed.
Lemma lem3326079 {A : Type'} (P : Prop) (Q : A -> Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3326080 {_86883 : Type'} (P : Prop) (Q : type686 _86883) : (term126 _86883 P Q) = (term127 _86883 P Q).
Proof. exact (@lem3326079 (_86883 -> Prop) P Q). Qed.
Lemma lem3326081 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term128 _86883 s P) = (term129 _86883 s P).
Proof. exact (@lem3326080 _86883 (term85 _86883 s P) (term108 _86883 s P)). Qed.
Lemma lem3326082 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term130 _86883 s P t) = (term98 _86883 s t P).
Proof. exact (eq_refl (term130 _86883 s P t)). Qed.
Lemma lem3326083 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term131 _86883 s P) = (term108 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326082 _86883 s t P)). Qed.
Lemma lem3326084 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326085 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term132 _86883 s P) = (term109 _86883 s P).
Proof. exact (MK_COMB (@lem3326084 _86883) (@lem3326083 _86883 s P)). Qed.
Lemma lem3326086 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term117 _86883 s P) = (term117 _86883 s P).
Proof. exact (eq_refl (term117 _86883 s P)). Qed.
Lemma lem3326087 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term128 _86883 s P) = (term119 _86883 s P).
Proof. exact (MK_COMB (@lem3326086 _86883 s P) (@lem3326085 _86883 s P)). Qed.
Lemma lem3326088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326089 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term133 _86883 s P) = (term134 _86883 s P).
Proof. exact (MK_COMB (@lem3326088) (@lem3326087 _86883 s P)). Qed.
Lemma lem3326090 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term130 _86883 s P t) = (term98 _86883 s t P).
Proof. exact (eq_refl (term130 _86883 s P t)). Qed.
Lemma lem3326091 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term117 _86883 s P) = (term117 _86883 s P).
Proof. exact (eq_refl (term117 _86883 s P)). Qed.
Lemma lem3326092 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term135 _86883 s P t) = (term136 _86883 s t P).
Proof. exact (MK_COMB (@lem3326091 _86883 s P) (@lem3326090 _86883 s t P)). Qed.
Lemma lem3326093 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term137 _86883 s P) = (term138 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326092 _86883 s t P)). Qed.
Lemma lem3326094 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326095 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term129 _86883 s P) = (term139 _86883 s P).
Proof. exact (MK_COMB (@lem3326094 _86883) (@lem3326093 _86883 s P)). Qed.
Lemma lem3326096 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term128 _86883 s P) = (term129 _86883 s P)) = ((term119 _86883 s P) = (term139 _86883 s P)).
Proof. exact (MK_COMB (@lem3326089 _86883 s P) (@lem3326095 _86883 s P)). Qed.
Lemma lem3326097 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term119 _86883 s P) = (term139 _86883 s P).
Proof. exact (EQ_MP (@lem3326096 _86883 s P) (@lem3326081 _86883 s P)). Qed.
Lemma lem3326099 {A : Type'} (P : Prop) (Q : A -> Prop) : (term124 A P Q) = (term125 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3326100 {_86883 : Type'} (P : Prop) (Q : _86883 -> Prop) : (term124 _86883 P Q) = (term125 _86883 P Q).
Proof. exact (@lem3326099 _86883 P Q). Qed.
Lemma lem3326101 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term140 _86883 s t P) = (term141 _86883 s t P).
Proof. exact (@lem3326100 _86883 (term85 _86883 s P) (term97 _86883 s t P)). Qed.
Lemma lem3326102 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term142 _86883 s t P x) = (term87 _86883 s t P x).
Proof. exact (eq_refl (term142 _86883 s t P x)). Qed.
Lemma lem3326103 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term143 _86883 s t P) = (term97 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326102 _86883 s t P x)). Qed.
Lemma lem3326104 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326105 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term144 _86883 s t P) = (term98 _86883 s t P).
Proof. exact (MK_COMB (@lem3326104 _86883) (@lem3326103 _86883 s t P)). Qed.
Lemma lem3326106 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term117 _86883 s P) = (term117 _86883 s P).
Proof. exact (eq_refl (term117 _86883 s P)). Qed.
Lemma lem3326107 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term140 _86883 s t P) = (term136 _86883 s t P).
Proof. exact (MK_COMB (@lem3326106 _86883 s P) (@lem3326105 _86883 s t P)). Qed.
Lemma lem3326108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326109 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term145 _86883 s t P) = (term146 _86883 s t P).
Proof. exact (MK_COMB (@lem3326108) (@lem3326107 _86883 s t P)). Qed.
Lemma lem3326110 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term142 _86883 s t P x) = (term87 _86883 s t P x).
Proof. exact (eq_refl (term142 _86883 s t P x)). Qed.
Lemma lem3326111 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term117 _86883 s P) = (term117 _86883 s P).
Proof. exact (eq_refl (term117 _86883 s P)). Qed.
Lemma lem3326112 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term147 _86883 s t P x) = (term148 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326111 _86883 s P) (@lem3326110 _86883 s t P x)). Qed.
Lemma lem3326113 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term149 _86883 s t P) = (term150 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326112 _86883 s t P x)). Qed.
Lemma lem3326114 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326115 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term141 _86883 s t P) = (term151 _86883 s t P).
Proof. exact (MK_COMB (@lem3326114 _86883) (@lem3326113 _86883 s t P)). Qed.
Lemma lem3326116 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : ((term140 _86883 s t P) = (term141 _86883 s t P)) = ((term136 _86883 s t P) = (term151 _86883 s t P)).
Proof. exact (MK_COMB (@lem3326109 _86883 s t P) (@lem3326115 _86883 s t P)). Qed.
Lemma lem3326117 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term136 _86883 s t P) = (term151 _86883 s t P).
Proof. exact (EQ_MP (@lem3326116 _86883 s t P) (@lem3326101 _86883 s t P)). Qed.
Lemma lem3326118 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term138 _86883 s P) = (term152 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326117 _86883 s t P)). Qed.
Lemma lem3326119 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326120 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term139 _86883 s P) = (term153 _86883 s P).
Proof. exact (MK_COMB (@lem3326119 _86883) (@lem3326118 _86883 s P)). Qed.
Lemma lem3326121 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term119 _86883 s P) = (term153 _86883 s P).
Proof. exact (TRANS (@lem3326097 _86883 s P) (@lem3326120 _86883 s P)). Qed.
Lemma lem3326122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326123 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term121 _86883 s P) = (term154 _86883 s P).
Proof. exact (MK_COMB (@lem3326122) (@lem3326121 _86883 s P)). Qed.
Lemma lem3326125 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3326126 {_86883 : Type'} (P : type686 _86883) (Q : Prop) : (term157 _86883 P Q) = (term158 _86883 P Q).
Proof. exact (@lem3326125 (_86883 -> Prop) P Q). Qed.
Lemma lem3326127 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term159 _86883 s P x) = (term160 _86883 s P x).
Proof. exact (@lem3326126 _86883 (term14 _86883 s x) (term67 _86883 P x)). Qed.
Lemma lem3326128 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term62 _86883 s x t) = (term12 _86883 s t x).
Proof. exact (eq_refl (term62 _86883 s x t)). Qed.
Lemma lem3326129 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term161 _86883 s x) = (term14 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326128 _86883 s t x)). Qed.
Lemma lem3326130 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326131 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term162 _86883 s x) = (term15 _86883 s x).
Proof. exact (MK_COMB (@lem3326130 _86883) (@lem3326129 _86883 s x)). Qed.
Lemma lem3326132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326133 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term163 _86883 s x) = (term68 _86883 s x).
Proof. exact (MK_COMB (@lem3326132) (@lem3326131 _86883 s x)). Qed.
Lemma lem3326134 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term67 _86883 P x) = (term67 _86883 P x).
Proof. exact (eq_refl (term67 _86883 P x)). Qed.
Lemma lem3326135 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term159 _86883 s P x) = (term69 _86883 s P x).
Proof. exact (MK_COMB (@lem3326133 _86883 s x) (@lem3326134 _86883 P x)). Qed.
Lemma lem3326136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326137 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term164 _86883 s P x) = (term165 _86883 s P x).
Proof. exact (MK_COMB (@lem3326136) (@lem3326135 _86883 s P x)). Qed.
Lemma lem3326138 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term62 _86883 s x t) = (term12 _86883 s t x).
Proof. exact (eq_refl (term62 _86883 s x t)). Qed.
Lemma lem3326139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326140 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term166 _86883 s x t) = (term167 _86883 s t x).
Proof. exact (MK_COMB (@lem3326139) (@lem3326138 _86883 s t x)). Qed.
Lemma lem3326141 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term67 _86883 P x) = (term67 _86883 P x).
Proof. exact (eq_refl (term67 _86883 P x)). Qed.
Lemma lem3326142 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term168 _86883 s t P x) = (term87 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326140 _86883 s t x) (@lem3326141 _86883 P x)). Qed.
Lemma lem3326143 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term169 _86883 s P x) = (term170 _86883 s P x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326142 _86883 s t P x)). Qed.
Lemma lem3326144 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326145 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term160 _86883 s P x) = (term171 _86883 s P x).
Proof. exact (MK_COMB (@lem3326144 _86883) (@lem3326143 _86883 s P x)). Qed.
Lemma lem3326146 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : ((term159 _86883 s P x) = (term160 _86883 s P x)) = ((term69 _86883 s P x) = (term171 _86883 s P x)).
Proof. exact (MK_COMB (@lem3326137 _86883 s P x) (@lem3326145 _86883 s P x)). Qed.
Lemma lem3326147 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term69 _86883 s P x) = (term171 _86883 s P x).
Proof. exact (EQ_MP (@lem3326146 _86883 s P x) (@lem3326127 _86883 s P x)). Qed.
Lemma lem3326148 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term82 _86883 s P) = (term172 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326147 _86883 s P x)). Qed.
Lemma lem3326149 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326150 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term83 _86883 s P) = (term173 _86883 s P).
Proof. exact (MK_COMB (@lem3326149 _86883) (@lem3326148 _86883 s P)). Qed.
Lemma lem3326151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326152 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term113 _86883 s P) = (term174 _86883 s P).
Proof. exact (MK_COMB (@lem3326151) (@lem3326150 _86883 s P)). Qed.
Lemma lem3326153 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term111 _86883 s P).
Proof. exact (eq_refl (term111 _86883 s P)). Qed.
Lemma lem3326154 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term115 _86883 s P) = (term175 _86883 s P).
Proof. exact (MK_COMB (@lem3326152 _86883 s P) (@lem3326153 _86883 s P)). Qed.
Lemma lem3326156 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3326157 {_86883 : Type'} (P : _86883 -> Prop) (Q : Prop) : (term155 _86883 P Q) = (term156 _86883 P Q).
Proof. exact (@lem3326156 _86883 P Q). Qed.
Lemma lem3326158 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term176 _86883 s P) = (term177 _86883 s P).
Proof. exact (@lem3326157 _86883 (term172 _86883 s P) (term111 _86883 s P)). Qed.
Lemma lem3326159 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term178 _86883 s P x) = (term171 _86883 s P x).
Proof. exact (eq_refl (term178 _86883 s P x)). Qed.
Lemma lem3326160 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term179 _86883 s P) = (term172 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326159 _86883 s P x)). Qed.
Lemma lem3326161 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326162 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term180 _86883 s P) = (term173 _86883 s P).
Proof. exact (MK_COMB (@lem3326161 _86883) (@lem3326160 _86883 s P)). Qed.
Lemma lem3326163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326164 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term181 _86883 s P) = (term174 _86883 s P).
Proof. exact (MK_COMB (@lem3326163) (@lem3326162 _86883 s P)). Qed.
Lemma lem3326165 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term111 _86883 s P).
Proof. exact (eq_refl (term111 _86883 s P)). Qed.
Lemma lem3326166 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term176 _86883 s P) = (term175 _86883 s P).
Proof. exact (MK_COMB (@lem3326164 _86883 s P) (@lem3326165 _86883 s P)). Qed.
Lemma lem3326167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326168 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term182 _86883 s P) = (term183 _86883 s P).
Proof. exact (MK_COMB (@lem3326167) (@lem3326166 _86883 s P)). Qed.
Lemma lem3326169 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term178 _86883 s P x) = (term171 _86883 s P x).
Proof. exact (eq_refl (term178 _86883 s P x)). Qed.
Lemma lem3326170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326171 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term184 _86883 s P x) = (term185 _86883 s P x).
Proof. exact (MK_COMB (@lem3326170) (@lem3326169 _86883 s P x)). Qed.
Lemma lem3326172 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term111 _86883 s P).
Proof. exact (eq_refl (term111 _86883 s P)). Qed.
Lemma lem3326173 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term186 _86883 x s P) = (term187 _86883 x s P).
Proof. exact (MK_COMB (@lem3326171 _86883 s P x) (@lem3326172 _86883 s P)). Qed.
Lemma lem3326174 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term188 _86883 s P) = (term189 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326173 _86883 x s P)). Qed.
Lemma lem3326175 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326176 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term177 _86883 s P) = (term190 _86883 s P).
Proof. exact (MK_COMB (@lem3326175 _86883) (@lem3326174 _86883 s P)). Qed.
Lemma lem3326177 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term176 _86883 s P) = (term177 _86883 s P)) = ((term175 _86883 s P) = (term190 _86883 s P)).
Proof. exact (MK_COMB (@lem3326168 _86883 s P) (@lem3326176 _86883 s P)). Qed.
Lemma lem3326178 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term175 _86883 s P) = (term190 _86883 s P).
Proof. exact (EQ_MP (@lem3326177 _86883 s P) (@lem3326158 _86883 s P)). Qed.
Lemma lem3326180 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3326181 {_86883 : Type'} (P : type686 _86883) (Q : Prop) : (term157 _86883 P Q) = (term158 _86883 P Q).
Proof. exact (@lem3326180 (_86883 -> Prop) P Q). Qed.
Lemma lem3326182 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term191 _86883 x s P) = (term192 _86883 x s P).
Proof. exact (@lem3326181 _86883 (term170 _86883 s P x) (term111 _86883 s P)). Qed.
Lemma lem3326183 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term193 _86883 s P x t) = (term87 _86883 s t P x).
Proof. exact (eq_refl (term193 _86883 s P x t)). Qed.
Lemma lem3326184 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term194 _86883 s P x) = (term170 _86883 s P x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326183 _86883 s t P x)). Qed.
Lemma lem3326185 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326186 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term195 _86883 s P x) = (term171 _86883 s P x).
Proof. exact (MK_COMB (@lem3326185 _86883) (@lem3326184 _86883 s P x)). Qed.
Lemma lem3326187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326188 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term196 _86883 s P x) = (term185 _86883 s P x).
Proof. exact (MK_COMB (@lem3326187) (@lem3326186 _86883 s P x)). Qed.
Lemma lem3326189 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term111 _86883 s P).
Proof. exact (eq_refl (term111 _86883 s P)). Qed.
Lemma lem3326190 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term191 _86883 x s P) = (term187 _86883 x s P).
Proof. exact (MK_COMB (@lem3326188 _86883 s P x) (@lem3326189 _86883 s P)). Qed.
Lemma lem3326191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326192 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term197 _86883 x s P) = (term198 _86883 x s P).
Proof. exact (MK_COMB (@lem3326191) (@lem3326190 _86883 x s P)). Qed.
Lemma lem3326193 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term193 _86883 s P x t) = (term87 _86883 s t P x).
Proof. exact (eq_refl (term193 _86883 s P x t)). Qed.
Lemma lem3326194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326195 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term199 _86883 s P x t) = (term200 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326194) (@lem3326193 _86883 s t P x)). Qed.
Lemma lem3326196 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term111 _86883 s P).
Proof. exact (eq_refl (term111 _86883 s P)). Qed.
Lemma lem3326197 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term201 _86883 x t s P) = (term202 _86883 t x s P).
Proof. exact (MK_COMB (@lem3326195 _86883 s t P x) (@lem3326196 _86883 s P)). Qed.
Lemma lem3326198 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term203 _86883 x s P) = (term204 _86883 x s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326197 _86883 t x s P)). Qed.
Lemma lem3326199 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326200 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term192 _86883 x s P) = (term205 _86883 x s P).
Proof. exact (MK_COMB (@lem3326199 _86883) (@lem3326198 _86883 x s P)). Qed.
Lemma lem3326201 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : ((term191 _86883 x s P) = (term192 _86883 x s P)) = ((term187 _86883 x s P) = (term205 _86883 x s P)).
Proof. exact (MK_COMB (@lem3326192 _86883 x s P) (@lem3326200 _86883 x s P)). Qed.
Lemma lem3326202 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term187 _86883 x s P) = (term205 _86883 x s P).
Proof. exact (EQ_MP (@lem3326201 _86883 x s P) (@lem3326182 _86883 x s P)). Qed.
Lemma lem3326203 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term189 _86883 s P) = (term206 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326202 _86883 x s P)). Qed.
Lemma lem3326204 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326205 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term190 _86883 s P) = (term207 _86883 s P).
Proof. exact (MK_COMB (@lem3326204 _86883) (@lem3326203 _86883 s P)). Qed.
Lemma lem3326206 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term175 _86883 s P) = (term207 _86883 s P).
Proof. exact (TRANS (@lem3326178 _86883 s P) (@lem3326205 _86883 s P)). Qed.
Lemma lem3326207 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term115 _86883 s P) = (term207 _86883 s P).
Proof. exact (TRANS (@lem3326154 _86883 s P) (@lem3326206 _86883 s P)). Qed.
Lemma lem3326208 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term123 _86883 s P) = (term208 _86883 s P).
Proof. exact (MK_COMB (@lem3326123 _86883 s P) (@lem3326207 _86883 s P)). Qed.
Lemma lem3326212 {A : Type'} (P : A -> Prop) (Q : Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3326213 {_86883 : Type'} (P : type686 _86883) (Q : Prop) : (term211 _86883 P Q) = (term212 _86883 P Q).
Proof. exact (@lem3326212 (_86883 -> Prop) P Q). Qed.
Lemma lem3326214 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term213 _86883 s P) = (term214 _86883 s P).
Proof. exact (@lem3326213 _86883 (term152 _86883 s P) (term207 _86883 s P)). Qed.
Lemma lem3326215 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term215 _86883 s P t) = (term151 _86883 s t P).
Proof. exact (eq_refl (term215 _86883 s P t)). Qed.
Lemma lem3326216 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term216 _86883 s P) = (term152 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326215 _86883 s t P)). Qed.
Lemma lem3326217 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326218 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term217 _86883 s P) = (term153 _86883 s P).
Proof. exact (MK_COMB (@lem3326217 _86883) (@lem3326216 _86883 s P)). Qed.
Lemma lem3326219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326220 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term218 _86883 s P) = (term154 _86883 s P).
Proof. exact (MK_COMB (@lem3326219) (@lem3326218 _86883 s P)). Qed.
Lemma lem3326221 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term207 _86883 s P) = (term207 _86883 s P).
Proof. exact (eq_refl (term207 _86883 s P)). Qed.
Lemma lem3326222 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term213 _86883 s P) = (term208 _86883 s P).
Proof. exact (MK_COMB (@lem3326220 _86883 s P) (@lem3326221 _86883 s P)). Qed.
Lemma lem3326223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326224 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term219 _86883 s P) = (term220 _86883 s P).
Proof. exact (MK_COMB (@lem3326223) (@lem3326222 _86883 s P)). Qed.
Lemma lem3326225 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term215 _86883 s P t) = (term151 _86883 s t P).
Proof. exact (eq_refl (term215 _86883 s P t)). Qed.
Lemma lem3326226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326227 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term221 _86883 s P t) = (term222 _86883 s t P).
Proof. exact (MK_COMB (@lem3326226) (@lem3326225 _86883 s t P)). Qed.
Lemma lem3326228 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term207 _86883 s P) = (term207 _86883 s P).
Proof. exact (eq_refl (term207 _86883 s P)). Qed.
Lemma lem3326229 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term223 _86883 t s P) = (term224 _86883 t s P).
Proof. exact (MK_COMB (@lem3326227 _86883 s t P) (@lem3326228 _86883 s P)). Qed.
Lemma lem3326230 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term225 _86883 s P) = (term226 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326229 _86883 t s P)). Qed.
Lemma lem3326231 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326232 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term214 _86883 s P) = (term227 _86883 s P).
Proof. exact (MK_COMB (@lem3326231 _86883) (@lem3326230 _86883 s P)). Qed.
Lemma lem3326233 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : ((term213 _86883 s P) = (term214 _86883 s P)) = ((term208 _86883 s P) = (term227 _86883 s P)).
Proof. exact (MK_COMB (@lem3326224 _86883 s P) (@lem3326232 _86883 s P)). Qed.
Lemma lem3326234 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term208 _86883 s P) = (term227 _86883 s P).
Proof. exact (EQ_MP (@lem3326233 _86883 s P) (@lem3326214 _86883 s P)). Qed.
Lemma lem3326236 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3326237 {_86883 : Type'} (P : _86883 -> Prop) (Q : _86883 -> Prop) : (term228 _86883 P Q) = (term229 _86883 P Q).
Proof. exact (@lem3326236 _86883 P Q). Qed.
Lemma lem3326238 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term230 _86883 t s P) = (term231 _86883 t s P).
Proof. exact (@lem3326237 _86883 (term150 _86883 s t P) (term206 _86883 s P)). Qed.
Lemma lem3326239 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term232 _86883 s t P x) = (term148 _86883 s t P x).
Proof. exact (eq_refl (term232 _86883 s t P x)). Qed.
Lemma lem3326240 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term233 _86883 s t P) = (term150 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326239 _86883 s t P x)). Qed.
Lemma lem3326241 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326242 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term234 _86883 s t P) = (term151 _86883 s t P).
Proof. exact (MK_COMB (@lem3326241 _86883) (@lem3326240 _86883 s t P)). Qed.
Lemma lem3326243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326244 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term235 _86883 s t P) = (term222 _86883 s t P).
Proof. exact (MK_COMB (@lem3326243) (@lem3326242 _86883 s t P)). Qed.
Lemma lem3326245 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term236 _86883 s P x) = (term205 _86883 x s P).
Proof. exact (eq_refl (term236 _86883 s P x)). Qed.
Lemma lem3326246 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term237 _86883 s P) = (term206 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326245 _86883 x s P)). Qed.
Lemma lem3326247 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326248 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term238 _86883 s P) = (term207 _86883 s P).
Proof. exact (MK_COMB (@lem3326247 _86883) (@lem3326246 _86883 s P)). Qed.
Lemma lem3326249 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term230 _86883 t s P) = (term224 _86883 t s P).
Proof. exact (MK_COMB (@lem3326244 _86883 s t P) (@lem3326248 _86883 s P)). Qed.
Lemma lem3326250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326251 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term239 _86883 t s P) = (term240 _86883 t s P).
Proof. exact (MK_COMB (@lem3326250) (@lem3326249 _86883 t s P)). Qed.
Lemma lem3326252 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term232 _86883 s t P x) = (term148 _86883 s t P x).
Proof. exact (eq_refl (term232 _86883 s t P x)). Qed.
Lemma lem3326253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326254 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term241 _86883 s t P x) = (term242 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326253) (@lem3326252 _86883 s t P x)). Qed.
Lemma lem3326255 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term236 _86883 s P x) = (term205 _86883 x s P).
Proof. exact (eq_refl (term236 _86883 s P x)). Qed.
Lemma lem3326256 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term243 _86883 t s P x) = (term244 _86883 t x s P).
Proof. exact (MK_COMB (@lem3326254 _86883 s t P x) (@lem3326255 _86883 x s P)). Qed.
Lemma lem3326257 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term245 _86883 t s P) = (term246 _86883 t s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326256 _86883 t x s P)). Qed.
Lemma lem3326258 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326259 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term231 _86883 t s P) = (term247 _86883 t s P).
Proof. exact (MK_COMB (@lem3326258 _86883) (@lem3326257 _86883 t s P)). Qed.
Lemma lem3326260 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : ((term230 _86883 t s P) = (term231 _86883 t s P)) = ((term224 _86883 t s P) = (term247 _86883 t s P)).
Proof. exact (MK_COMB (@lem3326251 _86883 t s P) (@lem3326259 _86883 t s P)). Qed.
Lemma lem3326261 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term224 _86883 t s P) = (term247 _86883 t s P).
Proof. exact (EQ_MP (@lem3326260 _86883 t s P) (@lem3326238 _86883 t s P)). Qed.
Lemma lem3326263 {A : Type'} (P : Prop) (Q : A -> Prop) : (term248 A P Q) = (term249 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3326264 {_86883 : Type'} (P : Prop) (Q : type686 _86883) : (term250 _86883 P Q) = (term251 _86883 P Q).
Proof. exact (@lem3326263 (_86883 -> Prop) P Q). Qed.
Lemma lem3326265 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term252 _86883 t x s P) = (term253 _86883 t x s P).
Proof. exact (@lem3326264 _86883 (term148 _86883 s t P x) (term204 _86883 x s P)). Qed.
Lemma lem3326266 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term254 _86883 x s P t) = (term202 _86883 t x s P).
Proof. exact (eq_refl (term254 _86883 x s P t)). Qed.
Lemma lem3326267 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term255 _86883 x s P) = (term204 _86883 x s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326266 _86883 t x s P)). Qed.
Lemma lem3326268 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326269 {_86883 : Type'} (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term256 _86883 x s P) = (term205 _86883 x s P).
Proof. exact (MK_COMB (@lem3326268 _86883) (@lem3326267 _86883 x s P)). Qed.
Lemma lem3326270 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term242 _86883 s t P x) = (term242 _86883 s t P x).
Proof. exact (eq_refl (term242 _86883 s t P x)). Qed.
Lemma lem3326271 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term252 _86883 t x s P) = (term244 _86883 t x s P).
Proof. exact (MK_COMB (@lem3326270 _86883 s t P x) (@lem3326269 _86883 x s P)). Qed.
Lemma lem3326272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326273 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term257 _86883 t x s P) = (term258 _86883 t x s P).
Proof. exact (MK_COMB (@lem3326272) (@lem3326271 _86883 t x s P)). Qed.
Lemma lem3326274 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term254 _86883 x s P t') = (term202 _86883 t' x s P).
Proof. exact (eq_refl (term254 _86883 x s P t')). Qed.
Lemma lem3326275 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term242 _86883 s t P x) = (term242 _86883 s t P x).
Proof. exact (eq_refl (term242 _86883 s t P x)). Qed.
Lemma lem3326276 {_86883 : Type'} (t : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term259 _86883 t x s P t') = (term260 _86883 t t' x s P).
Proof. exact (MK_COMB (@lem3326275 _86883 s t P x) (@lem3326274 _86883 t' x s P)). Qed.
Lemma lem3326277 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term261 _86883 t x s P) = (term262 _86883 t x s P).
Proof. exact (fun_ext (fun t' : _86883 -> Prop => @lem3326276 _86883 t t' x s P)). Qed.
Lemma lem3326278 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326279 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term253 _86883 t x s P) = (term263 _86883 t x s P).
Proof. exact (MK_COMB (@lem3326278 _86883) (@lem3326277 _86883 t x s P)). Qed.
Lemma lem3326280 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : ((term252 _86883 t x s P) = (term253 _86883 t x s P)) = ((term244 _86883 t x s P) = (term263 _86883 t x s P)).
Proof. exact (MK_COMB (@lem3326273 _86883 t x s P) (@lem3326279 _86883 t x s P)). Qed.
Lemma lem3326281 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term244 _86883 t x s P) = (term263 _86883 t x s P).
Proof. exact (EQ_MP (@lem3326280 _86883 t x s P) (@lem3326265 _86883 t x s P)). Qed.
Lemma lem3326282 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term246 _86883 t s P) = (term264 _86883 t s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326281 _86883 t x s P)). Qed.
Lemma lem3326283 {_86883 : Type'} : (@ex _86883) = (@ex _86883).
Proof. exact (eq_refl (@ex _86883)). Qed.
Lemma lem3326284 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term247 _86883 t s P) = (term265 _86883 t s P).
Proof. exact (MK_COMB (@lem3326283 _86883) (@lem3326282 _86883 t s P)). Qed.
Lemma lem3326285 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) : (term224 _86883 t s P) = (term265 _86883 t s P).
Proof. exact (TRANS (@lem3326261 _86883 t s P) (@lem3326284 _86883 t s P)). Qed.
Lemma lem3326286 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term226 _86883 s P) = (term266 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326285 _86883 t s P)). Qed.
Lemma lem3326287 {_86883 : Type'} : (@ex (_86883 -> Prop)) = (@ex (_86883 -> Prop)).
Proof. exact (eq_refl (@ex (_86883 -> Prop))). Qed.
Lemma lem3326288 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term227 _86883 s P) = (term267 _86883 s P).
Proof. exact (MK_COMB (@lem3326287 _86883) (@lem3326286 _86883 s P)). Qed.
Lemma lem3326289 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term208 _86883 s P) = (term267 _86883 s P).
Proof. exact (TRANS (@lem3326234 _86883 s P) (@lem3326288 _86883 s P)). Qed.
Lemma lem3326291 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term123 _86883 s P) = (term267 _86883 s P).
Proof. exact (TRANS (@lem3326208 _86883 s P) (@lem3326289 _86883 s P)). Qed.
Lemma lem3326292 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term55 _86883 s P) = (term267 _86883 s P).
Proof. exact (TRANS (@lem3325832 _86883 s P) (@lem3326291 _86883 s P)). Qed.
Lemma lem3326293 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (h1 : term55 _86883 s P) : term267 _86883 s P.
Proof. exact (EQ_MP (@lem3326292 _86883 s P) (@lem3325721 _86883 s P h1)). Qed.
Lemma lem3326294 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term265 _86883 t s P) : term265 _86883 t s P.
Proof. exact (h1). Qed.
Lemma lem3326295 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term263 _86883 t x s P) : term263 _86883 t x s P.
Proof. exact (h1). Qed.
Lemma lem3326296 {_86883 : Type'} (t : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term260 _86883 t t' x s P) : term260 _86883 t t' x s P.
Proof. exact (h1). Qed.
Lemma lem3326301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326302 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326301 _86883 Prop f x). Qed.
Lemma lem3326304 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326302 _86883 P x). Qed.
Lemma lem3326305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326311 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326310 _86883 Prop f x). Qed.
Lemma lem3326313 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (t x) = (@I (_86883 -> Prop) t x).
Proof. exact (@lem3326311 _86883 t x). Qed.
Lemma lem3326314 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (term67 _86883 t x) = (term268 _86883 t x).
Proof. exact (MK_COMB (@lem3326305) (@lem3326313 _86883 t x)). Qed.
Lemma lem3326315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326321 {_86883 : Type'} (f : type686 _86883) (x : _86883 -> Prop) : (f x) = (@I ((_86883 -> Prop) -> Prop) f x).
Proof. exact (@lem3326320 (_86883 -> Prop) Prop f x). Qed.
Lemma lem3326323 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (s t) = (@I ((_86883 -> Prop) -> Prop) s t).
Proof. exact (@lem3326321 _86883 s t). Qed.
Lemma lem3326324 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term269 _86883 s t) = (term270 _86883 s t).
Proof. exact (MK_COMB (@lem3326315) (@lem3326323 _86883 s t)). Qed.
Lemma lem3326325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326326 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term271 _86883 s t) = (term272 _86883 s t).
Proof. exact (MK_COMB (@lem3326325) (@lem3326324 _86883 s t)). Qed.
Lemma lem3326327 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term57 _86883 s t x) = (term273 _86883 s t x).
Proof. exact (MK_COMB (@lem3326326 _86883 s t) (@lem3326314 _86883 t x)). Qed.
Lemma lem3326328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326329 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term89 _86883 s t x) = (term274 _86883 s t x).
Proof. exact (MK_COMB (@lem3326328) (@lem3326327 _86883 s t x)). Qed.
Lemma lem3326330 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term91 _86883 s t P x) = (term275 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326329 _86883 s t x) (@lem3326304 _86883 P x)). Qed.
Lemma lem3326331 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term99 _86883 s t P) = (term276 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326330 _86883 s t P x)). Qed.
Lemma lem3326332 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3326333 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term100 _86883 s t P) = (term277 _86883 s t P).
Proof. exact (MK_COMB (@lem3326332 _86883) (@lem3326331 _86883 s t P)). Qed.
Lemma lem3326334 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term110 _86883 s P) = (term278 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326333 _86883 s t P)). Qed.
Lemma lem3326335 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326336 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term111 _86883 s P) = (term279 _86883 s P).
Proof. exact (MK_COMB (@lem3326335 _86883) (@lem3326334 _86883 s P)). Qed.
Lemma lem3326337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326343 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326342 _86883 Prop f x). Qed.
Lemma lem3326345 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326343 _86883 P x). Qed.
Lemma lem3326346 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term67 _86883 P x) = (term268 _86883 P x).
Proof. exact (MK_COMB (@lem3326337) (@lem3326345 _86883 P x)). Qed.
Lemma lem3326351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326352 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326351 _86883 Prop f x). Qed.
Lemma lem3326354 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) : (t' x) = (@I (_86883 -> Prop) t' x).
Proof. exact (@lem3326352 _86883 t' x). Qed.
Lemma lem3326359 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326360 {_86883 : Type'} (f : type686 _86883) (x : _86883 -> Prop) : (f x) = (@I ((_86883 -> Prop) -> Prop) f x).
Proof. exact (@lem3326359 (_86883 -> Prop) Prop f x). Qed.
Lemma lem3326362 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) : (s t') = (@I ((_86883 -> Prop) -> Prop) s t').
Proof. exact (@lem3326360 _86883 s t'). Qed.
Lemma lem3326363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326364 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) : (term10 _86883 s t') = (term280 _86883 s t').
Proof. exact (MK_COMB (@lem3326363) (@lem3326362 _86883 s t')). Qed.
Lemma lem3326365 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) (x : _86883) : (term12 _86883 s t' x) = (term281 _86883 s t' x).
Proof. exact (MK_COMB (@lem3326364 _86883 s t') (@lem3326354 _86883 t' x)). Qed.
Lemma lem3326366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326367 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) (x : _86883) : (term167 _86883 s t' x) = (term282 _86883 s t' x).
Proof. exact (MK_COMB (@lem3326366) (@lem3326365 _86883 s t' x)). Qed.
Lemma lem3326368 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term87 _86883 s t' P x) = (term283 _86883 s t' P x).
Proof. exact (MK_COMB (@lem3326367 _86883 s t' x) (@lem3326346 _86883 P x)). Qed.
Lemma lem3326369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326370 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term200 _86883 s t' P x) = (term284 _86883 s t' P x).
Proof. exact (MK_COMB (@lem3326369) (@lem3326368 _86883 s t' P x)). Qed.
Lemma lem3326371 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term202 _86883 t' x s P) = (term285 _86883 t' x s P).
Proof. exact (MK_COMB (@lem3326370 _86883 s t' P x) (@lem3326336 _86883 s P)). Qed.
Lemma lem3326372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326378 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326377 _86883 Prop f x). Qed.
Lemma lem3326380 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326378 _86883 P x). Qed.
Lemma lem3326381 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term67 _86883 P x) = (term268 _86883 P x).
Proof. exact (MK_COMB (@lem3326372) (@lem3326380 _86883 P x)). Qed.
Lemma lem3326386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326387 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326386 _86883 Prop f x). Qed.
Lemma lem3326389 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (t x) = (@I (_86883 -> Prop) t x).
Proof. exact (@lem3326387 _86883 t x). Qed.
Lemma lem3326394 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326395 {_86883 : Type'} (f : type686 _86883) (x : _86883 -> Prop) : (f x) = (@I ((_86883 -> Prop) -> Prop) f x).
Proof. exact (@lem3326394 (_86883 -> Prop) Prop f x). Qed.
Lemma lem3326397 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (s t) = (@I ((_86883 -> Prop) -> Prop) s t).
Proof. exact (@lem3326395 _86883 s t). Qed.
Lemma lem3326398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326399 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term10 _86883 s t) = (term280 _86883 s t).
Proof. exact (MK_COMB (@lem3326398) (@lem3326397 _86883 s t)). Qed.
Lemma lem3326400 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term12 _86883 s t x) = (term281 _86883 s t x).
Proof. exact (MK_COMB (@lem3326399 _86883 s t) (@lem3326389 _86883 t x)). Qed.
Lemma lem3326401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326402 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term167 _86883 s t x) = (term282 _86883 s t x).
Proof. exact (MK_COMB (@lem3326401) (@lem3326400 _86883 s t x)). Qed.
Lemma lem3326403 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term87 _86883 s t P x) = (term283 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326402 _86883 s t x) (@lem3326381 _86883 P x)). Qed.
Lemma lem3326408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326409 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326408 _86883 Prop f x). Qed.
Lemma lem3326411 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326409 _86883 P x). Qed.
Lemma lem3326412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326417 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326418 {_86883 : Type'} (f : _86883 -> Prop) (x : _86883) : (f x) = (@I (_86883 -> Prop) f x).
Proof. exact (@lem3326417 _86883 Prop f x). Qed.
Lemma lem3326420 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (t x) = (@I (_86883 -> Prop) t x).
Proof. exact (@lem3326418 _86883 t x). Qed.
Lemma lem3326421 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (term67 _86883 t x) = (term268 _86883 t x).
Proof. exact (MK_COMB (@lem3326412) (@lem3326420 _86883 t x)). Qed.
Lemma lem3326422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3326427 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3326428 {_86883 : Type'} (f : type686 _86883) (x : _86883 -> Prop) : (f x) = (@I ((_86883 -> Prop) -> Prop) f x).
Proof. exact (@lem3326427 (_86883 -> Prop) Prop f x). Qed.
Lemma lem3326430 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (s t) = (@I ((_86883 -> Prop) -> Prop) s t).
Proof. exact (@lem3326428 _86883 s t). Qed.
Lemma lem3326431 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term269 _86883 s t) = (term270 _86883 s t).
Proof. exact (MK_COMB (@lem3326422) (@lem3326430 _86883 s t)). Qed.
Lemma lem3326432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326433 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term271 _86883 s t) = (term272 _86883 s t).
Proof. exact (MK_COMB (@lem3326432) (@lem3326431 _86883 s t)). Qed.
Lemma lem3326434 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term57 _86883 s t x) = (term273 _86883 s t x).
Proof. exact (MK_COMB (@lem3326433 _86883 s t) (@lem3326421 _86883 t x)). Qed.
Lemma lem3326435 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term65 _86883 s x) = (term286 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326434 _86883 s t x)). Qed.
Lemma lem3326436 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326437 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term66 _86883 s x) = (term287 _86883 s x).
Proof. exact (MK_COMB (@lem3326436 _86883) (@lem3326435 _86883 s x)). Qed.
Lemma lem3326438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326439 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term72 _86883 s x) = (term288 _86883 s x).
Proof. exact (MK_COMB (@lem3326438) (@lem3326437 _86883 s x)). Qed.
Lemma lem3326440 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term74 _86883 s P x) = (term289 _86883 s P x).
Proof. exact (MK_COMB (@lem3326439 _86883 s x) (@lem3326411 _86883 P x)). Qed.
Lemma lem3326441 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term84 _86883 s P) = (term290 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326440 _86883 s P x)). Qed.
Lemma lem3326442 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3326443 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term85 _86883 s P) = (term291 _86883 s P).
Proof. exact (MK_COMB (@lem3326442 _86883) (@lem3326441 _86883 s P)). Qed.
Lemma lem3326444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326445 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term117 _86883 s P) = (term292 _86883 s P).
Proof. exact (MK_COMB (@lem3326444) (@lem3326443 _86883 s P)). Qed.
Lemma lem3326446 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term148 _86883 s t P x) = (term293 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326445 _86883 s P) (@lem3326403 _86883 s t P x)). Qed.
Lemma lem3326447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326448 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term242 _86883 s t P x) = (term294 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326447) (@lem3326446 _86883 s t P x)). Qed.
Lemma lem3326449 {_86883 : Type'} (t : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) : (term260 _86883 t t' x s P) = (term295 _86883 t t' x s P).
Proof. exact (MK_COMB (@lem3326448 _86883 s t P x) (@lem3326371 _86883 t' x s P)). Qed.
Lemma lem3326450 {_86883 : Type'} (t : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term260 _86883 t t' x s P) : term295 _86883 t t' x s P.
Proof. exact (EQ_MP (@lem3326449 _86883 t t' x s P) (@lem3326296 _86883 t t' x s P h1)). Qed.
Lemma lem3326451 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term293 _86883 s t P x.
Proof. exact (h1). Qed.
Lemma lem3326452 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term285 _86883 t' x s P.
Proof. exact (h1). Qed.
Lemma lem3326453 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term283 _86883 s t P x.
Proof. exact (proj2 (@lem3326451 _86883 s t P x h1)). Qed.
Lemma lem3326454 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term291 _86883 s P.
Proof. exact (proj1 (@lem3326451 _86883 s t P x h1)). Qed.
Lemma lem3326456 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term281 _86883 s t x.
Proof. exact (proj1 (@lem3326453 _86883 s t P x h1)). Qed.
Lemma lem3326459 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term279 _86883 s P.
Proof. exact (proj2 (@lem3326452 _86883 t' x s P h1)). Qed.
Lemma lem3326460 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term283 _86883 s t' P x.
Proof. exact (proj1 (@lem3326452 _86883 t' x s P h1)). Qed.
Lemma lem3326462 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term281 _86883 s t' x.
Proof. exact (proj1 (@lem3326460 _86883 t' x s P h1)). Qed.
Lemma lem3326466 {A : Type'} (P : A -> Prop) (Q : Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3326467 {_86883 : Type'} (P : type686 _86883) (Q : Prop) : (term298 _86883 P Q) = (term299 _86883 P Q).
Proof. exact (@lem3326466 (_86883 -> Prop) P Q). Qed.
Lemma lem3326468 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term300 _86883 s P x) = (term301 _86883 s P x).
Proof. exact (@lem3326467 _86883 (term286 _86883 s x) (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326469 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term302 _86883 s x t) = (term273 _86883 s t x).
Proof. exact (eq_refl (term302 _86883 s x t)). Qed.
Lemma lem3326470 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term303 _86883 s x) = (term286 _86883 s x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326469 _86883 s t x)). Qed.
Lemma lem3326471 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326472 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term304 _86883 s x) = (term287 _86883 s x).
Proof. exact (MK_COMB (@lem3326471 _86883) (@lem3326470 _86883 s x)). Qed.
Lemma lem3326473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326474 {_86883 : Type'} (s : type686 _86883) (x : _86883) : (term305 _86883 s x) = (term288 _86883 s x).
Proof. exact (MK_COMB (@lem3326473) (@lem3326472 _86883 s x)). Qed.
Lemma lem3326475 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (@I (_86883 -> Prop) P x) = (@I (_86883 -> Prop) P x).
Proof. exact (eq_refl (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326476 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term300 _86883 s P x) = (term289 _86883 s P x).
Proof. exact (MK_COMB (@lem3326474 _86883 s x) (@lem3326475 _86883 P x)). Qed.
Lemma lem3326477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326478 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term306 _86883 s P x) = (term307 _86883 s P x).
Proof. exact (MK_COMB (@lem3326477) (@lem3326476 _86883 s P x)). Qed.
Lemma lem3326479 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term302 _86883 s x t) = (term273 _86883 s t x).
Proof. exact (eq_refl (term302 _86883 s x t)). Qed.
Lemma lem3326480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3326481 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (x : _86883) : (term308 _86883 s x t) = (term274 _86883 s t x).
Proof. exact (MK_COMB (@lem3326480) (@lem3326479 _86883 s t x)). Qed.
Lemma lem3326482 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (@I (_86883 -> Prop) P x) = (@I (_86883 -> Prop) P x).
Proof. exact (eq_refl (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326483 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term309 _86883 s t P x) = (term275 _86883 s t P x).
Proof. exact (MK_COMB (@lem3326481 _86883 s t x) (@lem3326482 _86883 P x)). Qed.
Lemma lem3326484 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term310 _86883 s P x) = (term311 _86883 s P x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326483 _86883 s t P x)). Qed.
Lemma lem3326485 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326486 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term301 _86883 s P x) = (term312 _86883 s P x).
Proof. exact (MK_COMB (@lem3326485 _86883) (@lem3326484 _86883 s P x)). Qed.
Lemma lem3326487 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : ((term300 _86883 s P x) = (term301 _86883 s P x)) = ((term289 _86883 s P x) = (term312 _86883 s P x)).
Proof. exact (MK_COMB (@lem3326478 _86883 s P x) (@lem3326486 _86883 s P x)). Qed.
Lemma lem3326488 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term289 _86883 s P x) = (term312 _86883 s P x).
Proof. exact (EQ_MP (@lem3326487 _86883 s P x) (@lem3326468 _86883 s P x)). Qed.
Lemma lem3326489 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term290 _86883 s P) = (term313 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326488 _86883 s P x)). Qed.
Lemma lem3326490 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3326491 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term291 _86883 s P) = (term314 _86883 s P).
Proof. exact (MK_COMB (@lem3326490 _86883) (@lem3326489 _86883 s P)). Qed.
Lemma lem3326504 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term275 _86883 s t P x) = (term275 _86883 s t P x).
Proof. exact (eq_refl (term275 _86883 s t P x)). Qed.
Lemma lem3326505 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term311 _86883 s P x) = (term311 _86883 s P x).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326504 _86883 s t P x)). Qed.
Lemma lem3326506 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326507 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (x : _86883) : (term312 _86883 s P x) = (term312 _86883 s P x).
Proof. exact (MK_COMB (@lem3326506 _86883) (@lem3326505 _86883 s P x)). Qed.
Lemma lem3326508 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term313 _86883 s P) = (term313 _86883 s P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326507 _86883 s P x)). Qed.
Lemma lem3326509 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3326510 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term314 _86883 s P) = (term314 _86883 s P).
Proof. exact (MK_COMB (@lem3326509 _86883) (@lem3326508 _86883 s P)). Qed.
Lemma lem3326511 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term291 _86883 s P) = (term314 _86883 s P).
Proof. exact (TRANS (@lem3326491 _86883 s P) (@lem3326510 _86883 s P)). Qed.
Lemma lem3326512 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term314 _86883 s P.
Proof. exact (EQ_MP (@lem3326511 _86883 s P) (@lem3326454 _86883 s t P x h1)). Qed.
Lemma lem3326538 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) : (term275 _86883 s t P x) = (term275 _86883 s t P x).
Proof. exact (eq_refl (term275 _86883 s t P x)). Qed.
Lemma lem3326539 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term276 _86883 s t P) = (term276 _86883 s t P).
Proof. exact (fun_ext (fun x : _86883 => @lem3326538 _86883 s t P x)). Qed.
Lemma lem3326540 {_86883 : Type'} : (@all _86883) = (@all _86883).
Proof. exact (eq_refl (@all _86883)). Qed.
Lemma lem3326541 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) : (term277 _86883 s t P) = (term277 _86883 s t P).
Proof. exact (MK_COMB (@lem3326540 _86883) (@lem3326539 _86883 s t P)). Qed.
Lemma lem3326542 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term278 _86883 s P) = (term278 _86883 s P).
Proof. exact (fun_ext (fun t : _86883 -> Prop => @lem3326541 _86883 s t P)). Qed.
Lemma lem3326543 {_86883 : Type'} : (@all (_86883 -> Prop)) = (@all (_86883 -> Prop)).
Proof. exact (eq_refl (@all (_86883 -> Prop))). Qed.
Lemma lem3326545 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term279 _86883 s P) = (term279 _86883 s P).
Proof. exact (MK_COMB (@lem3326543 _86883) (@lem3326542 _86883 s P)). Qed.
Lemma lem3326546 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term279 _86883 s P.
Proof. exact (EQ_MP (@lem3326545 _86883 s P) (@lem3326459 _86883 t' x s P h1)). Qed.
Lemma lem3326559 {_86883 : Type'} (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term315 _86883 s P _34529.
Proof. exact (@lem3326512 _86883 s t P x h1 _34529). Qed.
Lemma lem3326560 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (_34529 : _86883) : (term315 _86883 s P _34529) = (term312 _86883 s P _34529).
Proof. exact (eq_refl (term315 _86883 s P _34529)). Qed.
Lemma lem3326561 {_86883 : Type'} (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term312 _86883 s P _34529.
Proof. exact (EQ_MP (@lem3326560 _86883 s P _34529) (@lem3326559 _86883 _34529 s t P x h1)). Qed.
Lemma lem3326562 {_86883 : Type'} (_34529 : _86883) (_34530 : _86883 -> Prop) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term316 _86883 s P _34529 _34530.
Proof. exact (@lem3326561 _86883 _34529 s t P x h1 _34530). Qed.
Lemma lem3326563 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term316 _86883 s P _34529 _34530) = (term275 _86883 s _34530 P _34529).
Proof. exact (eq_refl (term316 _86883 s P _34529 _34530)). Qed.
Lemma lem3326564 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term275 _86883 s _34530 P _34529.
Proof. exact (EQ_MP (@lem3326563 _86883 s _34530 P _34529) (@lem3326562 _86883 _34529 _34530 s t P x h1)). Qed.
Lemma lem3326565 {_86883 : Type'} (_34531 : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term317 _86883 s P _34531.
Proof. exact (@lem3326546 _86883 t' x s P h1 _34531). Qed.
Lemma lem3326566 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) : (term317 _86883 s P _34531) = (term277 _86883 s _34531 P).
Proof. exact (eq_refl (term317 _86883 s P _34531)). Qed.
Lemma lem3326567 {_86883 : Type'} (_34531 : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term277 _86883 s _34531 P.
Proof. exact (EQ_MP (@lem3326566 _86883 s _34531 P) (@lem3326565 _86883 _34531 t' x s P h1)). Qed.
Lemma lem3326568 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term318 _86883 s _34531 P _34532.
Proof. exact (@lem3326567 _86883 _34531 t' x s P h1 _34532). Qed.
Lemma lem3326569 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term318 _86883 s _34531 P _34532) = (term275 _86883 s _34531 P _34532).
Proof. exact (eq_refl (term318 _86883 s _34531 P _34532)). Qed.
Lemma lem3326570 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term275 _86883 s _34531 P _34532.
Proof. exact (EQ_MP (@lem3326569 _86883 s _34531 P _34532) (@lem3326568 _86883 _34531 _34532 t' x s P h1)). Qed.
Lemma lem3326581 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term275 _86883 s _34530 P _34529) = (term319 _86883 s _34530 P _34529).
Proof. exact (@lem3325385 (term270 _86883 s _34530) (term268 _86883 _34530 _34529) (@I (_86883 -> Prop) P _34529)). Qed.
Lemma lem3326582 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term319 _86883 s _34530 P _34529.
Proof. exact (EQ_MP (@lem3326581 _86883 s _34530 P _34529) (@lem3326564 _86883 _34530 _34529 s t P x h1)). Qed.
Lemma lem3326584 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term268 _86883 P x.
Proof. exact (proj2 (@lem3326453 _86883 s t P x h1)). Qed.
Lemma lem3326599 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term275 _86883 s _34531 P _34532) = (term319 _86883 s _34531 P _34532).
Proof. exact (@lem3325385 (term270 _86883 s _34531) (term268 _86883 _34531 _34532) (@I (_86883 -> Prop) P _34532)). Qed.
Lemma lem3326600 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term319 _86883 s _34531 P _34532.
Proof. exact (EQ_MP (@lem3326599 _86883 s _34531 P _34532) (@lem3326570 _86883 _34531 _34532 t' x s P h1)). Qed.
Lemma lem3326602 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term268 _86883 P x.
Proof. exact (proj2 (@lem3326460 _86883 t' x s P h1)). Qed.
Lemma lem3326608 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I ((_86883 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3326456 _86883 s t P x h1)). Qed.
Lemma lem3326609 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term320 _86883 s t.
Proof. exact (fun h0 : term270 _86883 s t => @lem3326608 _86883 s t P x h1). Qed.
Lemma lem3326611 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326612 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) : (term320 _86883 s t) = (@I ((_86883 -> Prop) -> Prop) s t).
Proof. exact (@lem3326611 (@I ((_86883 -> Prop) -> Prop) s t)). Qed.
Lemma lem3326613 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I ((_86883 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3326612 _86883 s t) (@lem3326609 _86883 s t P x h1)). Qed.
Lemma lem3326615 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I (_86883 -> Prop) t x.
Proof. exact (proj2 (@lem3326456 _86883 s t P x h1)). Qed.
Lemma lem3326616 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term322 _86883 t x.
Proof. exact (fun h0 : term268 _86883 t x => @lem3326615 _86883 s t P x h1). Qed.
Lemma lem3326618 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326619 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) : (term322 _86883 t x) = (@I (_86883 -> Prop) t x).
Proof. exact (@lem3326618 (@I (_86883 -> Prop) t x)). Qed.
Lemma lem3326620 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I (_86883 -> Prop) t x.
Proof. exact (EQ_MP (@lem3326619 _86883 t x) (@lem3326616 _86883 s t P x h1)). Qed.
Lemma lem3326626 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3326627 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term319 _86883 s _34530 P _34529) = (term323 _86883 s _34530 P _34529).
Proof. exact (@lem3326626 (term268 _86883 _34530 _34529) (term270 _86883 s _34530) (@I (_86883 -> Prop) P _34529)). Qed.
Lemma lem3326641 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3326642 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term324 _86883 s _34530 P _34529) = (term325 _86883 P _34529 s _34530).
Proof. exact (@lem3326641 (@I (_86883 -> Prop) P _34529) (term270 _86883 s _34530)). Qed.
Lemma lem3326648 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) : (term326 _86883 _34530 _34529) = (term326 _86883 _34530 _34529).
Proof. exact (eq_refl (term326 _86883 _34530 _34529)). Qed.
Lemma lem3326649 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term323 _86883 s _34530 P _34529) = (term327 _86883 P _34529 s _34530).
Proof. exact (MK_COMB (@lem3326648 _86883 _34530 _34529) (@lem3326642 _86883 P _34529 s _34530)). Qed.
Lemma lem3326653 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3326654 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term327 _86883 P _34529 s _34530) = (term328 _86883 P _34529 s _34530).
Proof. exact (@lem3326653 (@I (_86883 -> Prop) P _34529) (term268 _86883 _34530 _34529) (term270 _86883 s _34530)). Qed.
Lemma lem3326670 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term323 _86883 s _34530 P _34529) = (term328 _86883 P _34529 s _34530).
Proof. exact (TRANS (@lem3326649 _86883 P _34529 s _34530) (@lem3326654 _86883 P _34529 s _34530)). Qed.
Lemma lem3326671 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term319 _86883 s _34530 P _34529) = (term328 _86883 P _34529 s _34530).
Proof. exact (TRANS (@lem3326627 _86883 s _34530 P _34529) (@lem3326670 _86883 P _34529 s _34530)). Qed.
Lemma lem3326672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326673 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term329 _86883 s _34530 P _34529) = (term330 _86883 P _34529 s _34530).
Proof. exact (MK_COMB (@lem3326672) (@lem3326671 _86883 P _34529 s _34530)). Qed.
Lemma lem3326687 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3326688 {_86883 : Type'} (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term273 _86883 s _34530 _34529) = (term331 _86883 _34529 s _34530).
Proof. exact (@lem3326687 (term268 _86883 _34530 _34529) (term270 _86883 s _34530)). Qed.
Lemma lem3326694 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) : (term332 _86883 P _34529) = (term332 _86883 P _34529).
Proof. exact (eq_refl (term332 _86883 P _34529)). Qed.
Lemma lem3326695 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : (term333 _86883 P s _34530 _34529) = (term328 _86883 P _34529 s _34530).
Proof. exact (MK_COMB (@lem3326694 _86883 P _34529) (@lem3326688 _86883 _34529 s _34530)). Qed.
Lemma lem3326706 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : ((term319 _86883 s _34530 P _34529) = (term333 _86883 P s _34530 _34529)) = ((term328 _86883 P _34529 s _34530) = (term328 _86883 P _34529 s _34530)).
Proof. exact (MK_COMB (@lem3326673 _86883 P _34529 s _34530) (@lem3326695 _86883 P _34529 s _34530)). Qed.
Lemma lem3326708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3326709 (x : Prop) : (x = x) = True.
Proof. exact (@lem3326708 Prop x). Qed.
Lemma lem3326710 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (_34530 : _86883 -> Prop) : ((term328 _86883 P _34529 s _34530) = (term328 _86883 P _34529 s _34530)) = True.
Proof. exact (@lem3326709 (term328 _86883 P _34529 s _34530)). Qed.
Lemma lem3326711 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : ((term319 _86883 s _34530 P _34529) = (term333 _86883 P s _34530 _34529)) = True.
Proof. exact (TRANS (@lem3326706 _86883 P _34529 s _34530) (@lem3326710 _86883 P _34529 s _34530)). Qed.
Lemma lem3326712 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : True = ((term319 _86883 s _34530 P _34529) = (term333 _86883 P s _34530 _34529)).
Proof. exact (SYM (@lem3326711 _86883 P s _34530 _34529)). Qed.
Lemma lem3326713 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : (term319 _86883 s _34530 P _34529) = (term333 _86883 P s _34530 _34529).
Proof. exact (EQ_MP (@lem3326712 _86883 P s _34530 _34529) (@lem0)). Qed.
Lemma lem3326714 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term333 _86883 P s _34530 _34529.
Proof. exact (EQ_MP (@lem3326713 _86883 P s _34530 _34529) (@lem3326582 _86883 _34530 _34529 s t P x h1)). Qed.
Lemma lem3326716 (b : Prop) (a : Prop) : (a \/ b) = (term334 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3326717 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term333 _86883 P s _34530 _34529) = (term335 _86883 s _34530 P _34529).
Proof. exact (@lem3326716 (term273 _86883 s _34530 _34529) (@I (_86883 -> Prop) P _34529)). Qed.
Lemma lem3326719 (a : Prop) (b : Prop) : (term336 a b) = (term337 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3326720 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : (term338 _86883 s _34530 _34529) = (term339 _86883 s _34530 _34529).
Proof. exact (@lem3326719 (term270 _86883 s _34530) (term268 _86883 _34530 _34529)). Qed.
Lemma lem3326722 (a : Prop) : (term53 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3326723 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) : (term340 _86883 s _34530) = (@I ((_86883 -> Prop) -> Prop) s _34530).
Proof. exact (@lem3326722 (@I ((_86883 -> Prop) -> Prop) s _34530)). Qed.
Lemma lem3326724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326725 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) : (term341 _86883 s _34530) = (term280 _86883 s _34530).
Proof. exact (MK_COMB (@lem3326724) (@lem3326723 _86883 s _34530)). Qed.
Lemma lem3326727 (a : Prop) : (term53 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3326728 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) : (term342 _86883 _34530 _34529) = (@I (_86883 -> Prop) _34530 _34529).
Proof. exact (@lem3326727 (@I (_86883 -> Prop) _34530 _34529)). Qed.
Lemma lem3326729 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : (term339 _86883 s _34530 _34529) = (term281 _86883 s _34530 _34529).
Proof. exact (MK_COMB (@lem3326725 _86883 s _34530) (@lem3326728 _86883 _34530 _34529)). Qed.
Lemma lem3326730 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : (term338 _86883 s _34530 _34529) = (term281 _86883 s _34530 _34529).
Proof. exact (TRANS (@lem3326720 _86883 s _34530 _34529) (@lem3326729 _86883 s _34530 _34529)). Qed.
Lemma lem3326731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3326732 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (_34529 : _86883) : (term343 _86883 s _34530 _34529) = (term344 _86883 s _34530 _34529).
Proof. exact (MK_COMB (@lem3326731) (@lem3326730 _86883 s _34530 _34529)). Qed.
Lemma lem3326733 {_86883 : Type'} (P : _86883 -> Prop) (_34529 : _86883) : (@I (_86883 -> Prop) P _34529) = (@I (_86883 -> Prop) P _34529).
Proof. exact (eq_refl (@I (_86883 -> Prop) P _34529)). Qed.
Lemma lem3326734 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term335 _86883 s _34530 P _34529) = (term345 _86883 s _34530 P _34529).
Proof. exact (MK_COMB (@lem3326732 _86883 s _34530 _34529) (@lem3326733 _86883 P _34529)). Qed.
Lemma lem3326735 {_86883 : Type'} (s : type686 _86883) (_34530 : _86883 -> Prop) (P : _86883 -> Prop) (_34529 : _86883) : (term333 _86883 P s _34530 _34529) = (term345 _86883 s _34530 P _34529).
Proof. exact (TRANS (@lem3326717 _86883 s _34530 P _34529) (@lem3326734 _86883 s _34530 P _34529)). Qed.
Lemma lem3326737 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term281 _86883 s t x.
Proof. exact (conj (@lem3326613 _86883 s t P x h1) (@lem3326620 _86883 s t P x h1)). Qed.
Lemma lem3326739 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term345 _86883 s _34530 P _34529.
Proof. exact (EQ_MP (@lem3326735 _86883 s _34530 P _34529) (@lem3326714 _86883 _34530 _34529 s t P x h1)). Qed.
Lemma lem3326740 {_86883 : Type'} (_34530 : _86883 -> Prop) (_34529 : _86883) (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term345 _86883 s _34530 P _34529.
Proof. exact (@lem3326739 _86883 _34530 _34529 s t P x h1). Qed.
Lemma lem3326741 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term345 _86883 s t P x.
Proof. exact (@lem3326740 _86883 t x s t P x h1). Qed.
Lemma lem3326744 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I (_86883 -> Prop) P x.
Proof. exact (@lem3326741 _86883 s t P x h1 (@lem3326737 _86883 s t P x h1)). Qed.
Lemma lem3326745 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term322 _86883 P x.
Proof. exact (fun h0 : term268 _86883 P x => @lem3326744 _86883 s t P x h1). Qed.
Lemma lem3326747 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326748 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term322 _86883 P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326747 (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326749 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : @I (_86883 -> Prop) P x.
Proof. exact (EQ_MP (@lem3326748 _86883 P x) (@lem3326745 _86883 s t P x h1)). Qed.
Lemma lem3326752 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3326754 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term268 _86883 P x) = (term346 _86883 P x).
Proof. exact (@lem3326752 (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326757 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term346 _86883 P x.
Proof. exact (EQ_MP (@lem3326754 _86883 P x) (@lem3326584 _86883 s t P x h1)). Qed.
Lemma lem3326760 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : False.
Proof. exact (@lem3326757 _86883 s t P x h1 (@lem3326749 _86883 s t P x h1)). Qed.
Lemma lem3326761 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : term347.
Proof. exact (fun h0 : ~ False => @lem3326760 _86883 s t P x h1). Qed.
Lemma lem3326763 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326764 : term347 = False.
Proof. exact (@lem3326763 False). Qed.
Lemma lem3326765 {_86883 : Type'} (s : type686 _86883) (t : _86883 -> Prop) (P : _86883 -> Prop) (x : _86883) (h1 : term293 _86883 s t P x) : False.
Proof. exact (EQ_MP (@lem3326764) (@lem3326761 _86883 s t P x h1)). Qed.
Lemma lem3326767 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I ((_86883 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3326462 _86883 t' x s P h1)). Qed.
Lemma lem3326768 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term320 _86883 s t'.
Proof. exact (fun h0 : term270 _86883 s t' => @lem3326767 _86883 t' x s P h1). Qed.
Lemma lem3326770 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326771 {_86883 : Type'} (s : type686 _86883) (t' : _86883 -> Prop) : (term320 _86883 s t') = (@I ((_86883 -> Prop) -> Prop) s t').
Proof. exact (@lem3326770 (@I ((_86883 -> Prop) -> Prop) s t')). Qed.
Lemma lem3326772 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I ((_86883 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3326771 _86883 s t') (@lem3326768 _86883 t' x s P h1)). Qed.
Lemma lem3326774 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I (_86883 -> Prop) t' x.
Proof. exact (proj2 (@lem3326462 _86883 t' x s P h1)). Qed.
Lemma lem3326775 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term322 _86883 t' x.
Proof. exact (fun h0 : term268 _86883 t' x => @lem3326774 _86883 t' x s P h1). Qed.
Lemma lem3326777 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326778 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) : (term322 _86883 t' x) = (@I (_86883 -> Prop) t' x).
Proof. exact (@lem3326777 (@I (_86883 -> Prop) t' x)). Qed.
Lemma lem3326779 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I (_86883 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3326778 _86883 t' x) (@lem3326775 _86883 t' x s P h1)). Qed.
Lemma lem3326785 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3326786 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term319 _86883 s _34531 P _34532) = (term323 _86883 s _34531 P _34532).
Proof. exact (@lem3326785 (term268 _86883 _34531 _34532) (term270 _86883 s _34531) (@I (_86883 -> Prop) P _34532)). Qed.
Lemma lem3326800 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3326801 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term324 _86883 s _34531 P _34532) = (term325 _86883 P _34532 s _34531).
Proof. exact (@lem3326800 (@I (_86883 -> Prop) P _34532) (term270 _86883 s _34531)). Qed.
Lemma lem3326807 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) : (term326 _86883 _34531 _34532) = (term326 _86883 _34531 _34532).
Proof. exact (eq_refl (term326 _86883 _34531 _34532)). Qed.
Lemma lem3326808 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term323 _86883 s _34531 P _34532) = (term327 _86883 P _34532 s _34531).
Proof. exact (MK_COMB (@lem3326807 _86883 _34531 _34532) (@lem3326801 _86883 P _34532 s _34531)). Qed.
Lemma lem3326812 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3326813 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term327 _86883 P _34532 s _34531) = (term328 _86883 P _34532 s _34531).
Proof. exact (@lem3326812 (@I (_86883 -> Prop) P _34532) (term268 _86883 _34531 _34532) (term270 _86883 s _34531)). Qed.
Lemma lem3326829 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term323 _86883 s _34531 P _34532) = (term328 _86883 P _34532 s _34531).
Proof. exact (TRANS (@lem3326808 _86883 P _34532 s _34531) (@lem3326813 _86883 P _34532 s _34531)). Qed.
Lemma lem3326830 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term319 _86883 s _34531 P _34532) = (term328 _86883 P _34532 s _34531).
Proof. exact (TRANS (@lem3326786 _86883 s _34531 P _34532) (@lem3326829 _86883 P _34532 s _34531)). Qed.
Lemma lem3326831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3326832 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term329 _86883 s _34531 P _34532) = (term330 _86883 P _34532 s _34531).
Proof. exact (MK_COMB (@lem3326831) (@lem3326830 _86883 P _34532 s _34531)). Qed.
Lemma lem3326846 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3326847 {_86883 : Type'} (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term273 _86883 s _34531 _34532) = (term331 _86883 _34532 s _34531).
Proof. exact (@lem3326846 (term268 _86883 _34531 _34532) (term270 _86883 s _34531)). Qed.
Lemma lem3326853 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) : (term332 _86883 P _34532) = (term332 _86883 P _34532).
Proof. exact (eq_refl (term332 _86883 P _34532)). Qed.
Lemma lem3326854 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : (term333 _86883 P s _34531 _34532) = (term328 _86883 P _34532 s _34531).
Proof. exact (MK_COMB (@lem3326853 _86883 P _34532) (@lem3326847 _86883 _34532 s _34531)). Qed.
Lemma lem3326865 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : ((term319 _86883 s _34531 P _34532) = (term333 _86883 P s _34531 _34532)) = ((term328 _86883 P _34532 s _34531) = (term328 _86883 P _34532 s _34531)).
Proof. exact (MK_COMB (@lem3326832 _86883 P _34532 s _34531) (@lem3326854 _86883 P _34532 s _34531)). Qed.
Lemma lem3326867 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3326868 (x : Prop) : (x = x) = True.
Proof. exact (@lem3326867 Prop x). Qed.
Lemma lem3326869 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) (s : type686 _86883) (_34531 : _86883 -> Prop) : ((term328 _86883 P _34532 s _34531) = (term328 _86883 P _34532 s _34531)) = True.
Proof. exact (@lem3326868 (term328 _86883 P _34532 s _34531)). Qed.
Lemma lem3326870 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : ((term319 _86883 s _34531 P _34532) = (term333 _86883 P s _34531 _34532)) = True.
Proof. exact (TRANS (@lem3326865 _86883 P _34532 s _34531) (@lem3326869 _86883 P _34532 s _34531)). Qed.
Lemma lem3326871 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : True = ((term319 _86883 s _34531 P _34532) = (term333 _86883 P s _34531 _34532)).
Proof. exact (SYM (@lem3326870 _86883 P s _34531 _34532)). Qed.
Lemma lem3326872 {_86883 : Type'} (P : _86883 -> Prop) (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : (term319 _86883 s _34531 P _34532) = (term333 _86883 P s _34531 _34532).
Proof. exact (EQ_MP (@lem3326871 _86883 P s _34531 _34532) (@lem0)). Qed.
Lemma lem3326873 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term333 _86883 P s _34531 _34532.
Proof. exact (EQ_MP (@lem3326872 _86883 P s _34531 _34532) (@lem3326600 _86883 _34531 _34532 t' x s P h1)). Qed.
Lemma lem3326875 (b : Prop) (a : Prop) : (a \/ b) = (term334 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3326876 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term333 _86883 P s _34531 _34532) = (term335 _86883 s _34531 P _34532).
Proof. exact (@lem3326875 (term273 _86883 s _34531 _34532) (@I (_86883 -> Prop) P _34532)). Qed.
Lemma lem3326878 (a : Prop) (b : Prop) : (term336 a b) = (term337 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3326879 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : (term338 _86883 s _34531 _34532) = (term339 _86883 s _34531 _34532).
Proof. exact (@lem3326878 (term270 _86883 s _34531) (term268 _86883 _34531 _34532)). Qed.
Lemma lem3326881 (a : Prop) : (term53 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3326882 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) : (term340 _86883 s _34531) = (@I ((_86883 -> Prop) -> Prop) s _34531).
Proof. exact (@lem3326881 (@I ((_86883 -> Prop) -> Prop) s _34531)). Qed.
Lemma lem3326883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3326884 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) : (term341 _86883 s _34531) = (term280 _86883 s _34531).
Proof. exact (MK_COMB (@lem3326883) (@lem3326882 _86883 s _34531)). Qed.
Lemma lem3326886 (a : Prop) : (term53 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3326887 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) : (term342 _86883 _34531 _34532) = (@I (_86883 -> Prop) _34531 _34532).
Proof. exact (@lem3326886 (@I (_86883 -> Prop) _34531 _34532)). Qed.
Lemma lem3326888 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : (term339 _86883 s _34531 _34532) = (term281 _86883 s _34531 _34532).
Proof. exact (MK_COMB (@lem3326884 _86883 s _34531) (@lem3326887 _86883 _34531 _34532)). Qed.
Lemma lem3326889 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : (term338 _86883 s _34531 _34532) = (term281 _86883 s _34531 _34532).
Proof. exact (TRANS (@lem3326879 _86883 s _34531 _34532) (@lem3326888 _86883 s _34531 _34532)). Qed.
Lemma lem3326890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3326891 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (_34532 : _86883) : (term343 _86883 s _34531 _34532) = (term344 _86883 s _34531 _34532).
Proof. exact (MK_COMB (@lem3326890) (@lem3326889 _86883 s _34531 _34532)). Qed.
Lemma lem3326892 {_86883 : Type'} (P : _86883 -> Prop) (_34532 : _86883) : (@I (_86883 -> Prop) P _34532) = (@I (_86883 -> Prop) P _34532).
Proof. exact (eq_refl (@I (_86883 -> Prop) P _34532)). Qed.
Lemma lem3326893 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term335 _86883 s _34531 P _34532) = (term345 _86883 s _34531 P _34532).
Proof. exact (MK_COMB (@lem3326891 _86883 s _34531 _34532) (@lem3326892 _86883 P _34532)). Qed.
Lemma lem3326894 {_86883 : Type'} (s : type686 _86883) (_34531 : _86883 -> Prop) (P : _86883 -> Prop) (_34532 : _86883) : (term333 _86883 P s _34531 _34532) = (term345 _86883 s _34531 P _34532).
Proof. exact (TRANS (@lem3326876 _86883 s _34531 P _34532) (@lem3326893 _86883 s _34531 P _34532)). Qed.
Lemma lem3326896 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term281 _86883 s t' x.
Proof. exact (conj (@lem3326772 _86883 t' x s P h1) (@lem3326779 _86883 t' x s P h1)). Qed.
Lemma lem3326898 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term345 _86883 s _34531 P _34532.
Proof. exact (EQ_MP (@lem3326894 _86883 s _34531 P _34532) (@lem3326873 _86883 _34531 _34532 t' x s P h1)). Qed.
Lemma lem3326899 {_86883 : Type'} (_34531 : _86883 -> Prop) (_34532 : _86883) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term345 _86883 s _34531 P _34532.
Proof. exact (@lem3326898 _86883 _34531 _34532 t' x s P h1). Qed.
Lemma lem3326900 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term345 _86883 s t' P x.
Proof. exact (@lem3326899 _86883 t' x t' x s P h1). Qed.
Lemma lem3326903 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I (_86883 -> Prop) P x.
Proof. exact (@lem3326900 _86883 t' x s P h1 (@lem3326896 _86883 t' x s P h1)). Qed.
Lemma lem3326904 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term322 _86883 P x.
Proof. exact (fun h0 : term268 _86883 P x => @lem3326903 _86883 t' x s P h1). Qed.
Lemma lem3326906 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326907 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term322 _86883 P x) = (@I (_86883 -> Prop) P x).
Proof. exact (@lem3326906 (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326908 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : @I (_86883 -> Prop) P x.
Proof. exact (EQ_MP (@lem3326907 _86883 P x) (@lem3326904 _86883 t' x s P h1)). Qed.
Lemma lem3326911 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3326913 {_86883 : Type'} (P : _86883 -> Prop) (x : _86883) : (term268 _86883 P x) = (term346 _86883 P x).
Proof. exact (@lem3326911 (@I (_86883 -> Prop) P x)). Qed.
Lemma lem3326916 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term346 _86883 P x.
Proof. exact (EQ_MP (@lem3326913 _86883 P x) (@lem3326602 _86883 t' x s P h1)). Qed.
Lemma lem3326919 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : False.
Proof. exact (@lem3326916 _86883 t' x s P h1 (@lem3326908 _86883 t' x s P h1)). Qed.
Lemma lem3326920 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : term347.
Proof. exact (fun h0 : ~ False => @lem3326919 _86883 t' x s P h1). Qed.
Lemma lem3326922 (p : Prop) : (term321 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3326923 : term347 = False.
Proof. exact (@lem3326922 False). Qed.
Lemma lem3326924 {_86883 : Type'} (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term285 _86883 t' x s P) : False.
Proof. exact (EQ_MP (@lem3326923) (@lem3326920 _86883 t' x s P h1)). Qed.
Lemma lem3326925 {_86883 : Type'} (t : _86883 -> Prop) (t' : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term260 _86883 t t' x s P) : False.
Proof. exact (or_elim (@lem3326450 _86883 t t' x s P h1) (fun h0 : term293 _86883 s t P x => @lem3326765 _86883 s t P x h0) (fun h0 : term285 _86883 t' x s P => @lem3326924 _86883 t' x s P h0)). Qed.
Lemma lem3326926 {_86883 : Type'} (t : _86883 -> Prop) (x : _86883) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term263 _86883 t x s P) : False.
Proof. exact (ex_elim (@lem3326295 _86883 t x s P h1) (fun t' : _86883 -> Prop => fun h0 : term262 _86883 t x s P t' => @lem3326925 _86883 t t' x s P h0)). Qed.
Lemma lem3326927 {_86883 : Type'} (t : _86883 -> Prop) (s : type686 _86883) (P : _86883 -> Prop) (h1 : term265 _86883 t s P) : False.
Proof. exact (ex_elim (@lem3326294 _86883 t s P h1) (fun x : _86883 => fun h0 : term264 _86883 t s P x => @lem3326926 _86883 t x s P h0)). Qed.
Lemma lem3326928 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (h1 : term55 _86883 s P) : False.
Proof. exact (ex_elim (@lem3326293 _86883 s P h1) (fun t : _86883 -> Prop => fun h0 : term266 _86883 s P t => @lem3326927 _86883 t s P h0)). Qed.
Lemma lem3326929 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (h1 : term55 _86883 s P) : (term55 _86883 s P) = False.
Proof. exact (prop_ext (fun h2 : term55 _86883 s P => @lem3326928 _86883 s P h1) (fun h2 : False => @lem3325721 _86883 s P h1)). Qed.
Lemma lem3326930 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) (h1 : term55 _86883 s P) : False.
Proof. exact (EQ_MP (@lem3326929 _86883 s P h1) (@lem3325721 _86883 s P h1)). Qed.
Lemma lem3326931 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : term54 _86883 s P.
Proof. exact (fun h0 : term55 _86883 s P => @lem3326930 _86883 s P h0). Qed.
Lemma lem3326932 {_86883 : Type'} (s : type686 _86883) (P : _86883 -> Prop) : (term23 _86883 s P) = (term37 _86883 s P).
Proof. exact (EQ_MP (@lem3325720 _86883 s P) (@lem3326931 _86883 s P)). Qed.
Lemma lem3326937 {_86883 : Type'} (P : _86883 -> Prop) : term41 _86883 P.
Proof. exact (fun s : type686 _86883 => @lem3326932 _86883 s P). Qed.
Lemma lem3326942 {_86883 : Type'} : term45 _86883.
Proof. exact (fun P : _86883 -> Prop => @lem3326937 _86883 P). Qed.
Lemma lem3326943 {_86883 : Type'} : term47 _86883.
Proof. exact (EQ_MP (@lem3325716 _86883) (@lem3326942 _86883)). Qed.
Lemma lem3326945 {_86883 : Type'} : term47 _86883.
Proof. exact (@lem3325562 _86883 (@lem3326943 _86883)). Qed.
Lemma lem3326946 {_86883 : Type'} (h1 : term48 _86883) : False.
Proof. exact (@lem3326945 _86883 (@lem3325546 _86883 h1)). Qed.
Lemma lem3326947 {_86883 : Type'} (h1 : term48 _86883) : (term48 _86883) = False.
Proof. exact (prop_ext (fun h2 : term48 _86883 => @lem3326946 _86883 h1) (fun h2 : False => @lem3325546 _86883 h1)). Qed.
Lemma lem3326948 {_86883 : Type'} (h1 : term48 _86883) : False.
Proof. exact (EQ_MP (@lem3326947 _86883 h1) (@lem3325546 _86883 h1)). Qed.
Lemma lem3326949 {_86883 : Type'} : term47 _86883.
Proof. exact (fun h0 : term48 _86883 => @lem3326948 _86883 h0). Qed.
Lemma lem3326950 {_86883 : Type'} : term45 _86883.
Proof. exact (EQ_MP (@lem3325545 _86883) (@lem3326949 _86883)). Qed.
Lemma lem3326952 {_86883 : Type'} : term44 _86883.
Proof. exact (EQ_MP (@lem3325541 _86883) (@lem3326950 _86883)). Qed.
