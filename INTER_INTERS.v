Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_INTERS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INTER_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3354637_spec.
Require Import thm3354697_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem3480369 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3480370 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (s : A -> Prop) (f : type686 A) (_477 : A -> Prop) : (term2 A s f _475 _474 _477) = (term3 A _474 _475 s f _477).
Proof. exact (@lem3480369 A _474 _475 (term4 A s f) _477). Qed.
Lemma lem3480371 {A : Type'} (f : type686 A) (s : A -> Prop) : (term5 A f s) = (term6 A f s).
Proof. exact (@lem3480370 A s (f = (@EMPTY (A -> Prop))) s f (term7 A f s)). Qed.
Lemma lem3480372 {A : Type'} (f : type686 A) (s : A -> Prop) : (term8 A f s) = ((term9 A s f) = (term7 A f s)).
Proof. exact (eq_refl (term8 A f s)). Qed.
Lemma lem3480373 {A : Type'} (f : type686 A) : (term10 A f) = (term10 A f).
Proof. exact (eq_refl (term10 A f)). Qed.
Lemma lem3480374 {A : Type'} (f : type686 A) (s : A -> Prop) : (term11 A f s) = (term12 A f s).
Proof. exact (MK_COMB (@lem3480373 A f) (@lem3480372 A f s)). Qed.
Lemma lem3480375 {A : Type'} (f : type686 A) (s : A -> Prop) : (term13 A f s) = ((term9 A s f) = s).
Proof. exact (eq_refl (term13 A f s)). Qed.
Lemma lem3480376 {A : Type'} (f : type686 A) : (term14 A f) = (term14 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem3480377 {A : Type'} (f : type686 A) (s : A -> Prop) : (term15 A f s) = (term16 A f s).
Proof. exact (MK_COMB (@lem3480376 A f) (@lem3480375 A f s)). Qed.
Lemma lem3480378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3480379 {A : Type'} (f : type686 A) (s : A -> Prop) : (term17 A f s) = (term18 A f s).
Proof. exact (MK_COMB (@lem3480378) (@lem3480377 A f s)). Qed.
Lemma lem3480380 {A : Type'} (f : type686 A) (s : A -> Prop) : (term6 A f s) = (term19 A f s).
Proof. exact (MK_COMB (@lem3480379 A f s) (@lem3480374 A f s)). Qed.
Lemma lem3480381 {A : Type'} (f : type686 A) (s : A -> Prop) : (term5 A f s) = ((term9 A s f) = (term20 A f s)).
Proof. exact (eq_refl (term5 A f s)). Qed.
Lemma lem3480382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480383 {A : Type'} (f : type686 A) (s : A -> Prop) : (term21 A f s) = (term22 A f s).
Proof. exact (MK_COMB (@lem3480382) (@lem3480381 A f s)). Qed.
Lemma lem3480384 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term5 A f s) = (term6 A f s)) = (((term9 A s f) = (term20 A f s)) = (term19 A f s)).
Proof. exact (MK_COMB (@lem3480383 A f s) (@lem3480380 A f s)). Qed.
Lemma lem3480385 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term9 A s f) = (term20 A f s)) = (term19 A f s).
Proof. exact (EQ_MP (@lem3480384 A f s) (@lem3480371 A f s)). Qed.
Lemma lem3480386 {A : Type'} (f : type686 A) (s : A -> Prop) : (term19 A f s) = ((term9 A s f) = (term20 A f s)).
Proof. exact (SYM (@lem3480385 A f s)). Qed.
Lemma lem3480387 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3480404 {A : Type'} (f : type686 A) (h1 : term23 A f) : term23 A f.
Proof. exact (h1). Qed.
Lemma lem3480421 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3480422 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (f : type686 A) (s : A -> Prop) (_477 : A -> Prop) : (term24 A f s _475 _474 _477) = (term25 A _474 _475 f s _477).
Proof. exact (@lem3480421 A _474 _475 (term26 A f s) _477). Qed.
Lemma lem3480423 {A : Type'} (f : type686 A) (s : A -> Prop) : (term27 A f s) = (term28 A f s).
Proof. exact (@lem3480422 A s (f = (@EMPTY (A -> Prop))) f s (term29 A f s)). Qed.
Lemma lem3480424 {A : Type'} (f : type686 A) (s : A -> Prop) : (term30 A f s) = ((term31 A f s) = (term29 A f s)).
Proof. exact (eq_refl (term30 A f s)). Qed.
Lemma lem3480425 {A : Type'} (f : type686 A) : (term10 A f) = (term10 A f).
Proof. exact (eq_refl (term10 A f)). Qed.
Lemma lem3480426 {A : Type'} (f : type686 A) (s : A -> Prop) : (term32 A f s) = (term33 A f s).
Proof. exact (MK_COMB (@lem3480425 A f) (@lem3480424 A f s)). Qed.
Lemma lem3480427 {A : Type'} (f : type686 A) (s : A -> Prop) : (term34 A f s) = ((term31 A f s) = s).
Proof. exact (eq_refl (term34 A f s)). Qed.
Lemma lem3480428 {A : Type'} (f : type686 A) : (term14 A f) = (term14 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem3480429 {A : Type'} (f : type686 A) (s : A -> Prop) : (term35 A f s) = (term36 A f s).
Proof. exact (MK_COMB (@lem3480428 A f) (@lem3480427 A f s)). Qed.
Lemma lem3480430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3480431 {A : Type'} (f : type686 A) (s : A -> Prop) : (term37 A f s) = (term38 A f s).
Proof. exact (MK_COMB (@lem3480430) (@lem3480429 A f s)). Qed.
Lemma lem3480432 {A : Type'} (f : type686 A) (s : A -> Prop) : (term28 A f s) = (term39 A f s).
Proof. exact (MK_COMB (@lem3480431 A f s) (@lem3480426 A f s)). Qed.
Lemma lem3480433 {A : Type'} (f : type686 A) (s : A -> Prop) : (term27 A f s) = ((term31 A f s) = (term40 A f s)).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3480434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480435 {A : Type'} (f : type686 A) (s : A -> Prop) : (term41 A f s) = (term42 A f s).
Proof. exact (MK_COMB (@lem3480434) (@lem3480433 A f s)). Qed.
Lemma lem3480436 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term27 A f s) = (term28 A f s)) = (((term31 A f s) = (term40 A f s)) = (term39 A f s)).
Proof. exact (MK_COMB (@lem3480435 A f s) (@lem3480432 A f s)). Qed.
Lemma lem3480437 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term31 A f s) = (term40 A f s)) = (term39 A f s).
Proof. exact (EQ_MP (@lem3480436 A f s) (@lem3480423 A f s)). Qed.
Lemma lem3480438 {A : Type'} (f : type686 A) (s : A -> Prop) : (term39 A f s) = ((term31 A f s) = (term40 A f s)).
Proof. exact (SYM (@lem3480437 A f s)). Qed.
Lemma lem3480439 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3480456 {A : Type'} (f : type686 A) (h1 : term23 A f) : term23 A f.
Proof. exact (h1). Qed.
Lemma lem3480495 {A : Type'} : term43 A.
Proof. exact (proj2 (@lem3258568 A)). Qed.
Lemma lem3480496 {A : Type'} (s : A -> Prop) : term44 A s.
Proof. exact (@lem3480495 A s). Qed.
Lemma lem3480497 {A : Type'} (s : A -> Prop) : (term44 A s) = ((@INTER A s (@UNIV A)) = s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem3480506 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3480507 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3480508 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@INTERS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3480507 A) (@lem3480506 A f h1)). Qed.
Lemma lem3480510 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem3480511 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@UNIV A).
Proof. exact (TRANS (@lem3480508 A f h1) (@lem3480510 A)). Qed.
Lemma lem3480512 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@INTER A s).
Proof. exact (eq_refl (@INTER A s)). Qed.
Lemma lem3480513 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term9 A s f) = (@INTER A s (@UNIV A)).
Proof. exact (MK_COMB (@lem3480512 A s) (@lem3480511 A f h1)). Qed.
Lemma lem3480515 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (EQ_MP (@lem3480497 A s) (@lem3480496 A s)). Qed.
Lemma lem3480516 {A : Type'} (s : A -> Prop) : (@INTER A s (@UNIV A)) = s.
Proof. exact (@lem3480515 A s). Qed.
Lemma lem3480517 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term9 A s f) = s.
Proof. exact (TRANS (@lem3480513 A s f h1) (@lem3480516 A s)). Qed.
Lemma lem3480518 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3480519 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term45 A s f) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem3480518 A) (@lem3480517 A s f h1)). Qed.
Lemma lem3480520 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3480521 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term9 A s f) = s) = (s = s).
Proof. exact (MK_COMB (@lem3480519 A s f h1) (@lem3480520 A s)). Qed.
Lemma lem3480523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3480524 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3480523 (A -> Prop) x). Qed.
Lemma lem3480525 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem3480524 A s). Qed.
Lemma lem3480526 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term9 A s f) = s) = True.
Proof. exact (TRANS (@lem3480521 A s f h1) (@lem3480525 A s)). Qed.
Lemma lem3480527 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : True = ((term9 A s f) = s).
Proof. exact (SYM (@lem3480526 A s f h1)). Qed.
Lemma lem3480544 {_89711 _89725 : Type'} : term46 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3480545 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term47 _89711 _89725 P.
Proof. exact (@lem3480544 _89711 _89725 P). Qed.
Lemma lem3480546 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term47 _89711 _89725 P) = (term48 _89711 _89725 P).
Proof. exact (eq_refl (term47 _89711 _89725 P)). Qed.
Lemma lem3480547 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term48 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3480546 _89711 _89725 P) (@lem3480545 _89711 _89725 P)). Qed.
Lemma lem3480548 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term49 _89711 _89725 P f.
Proof. exact (@lem3480547 _89711 _89725 P f). Qed.
Lemma lem3480549 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term49 _89711 _89725 P f) = ((term50 _89711 _89725 P f) = (term51 _89711 _89725 P f)).
Proof. exact (eq_refl (term49 _89711 _89725 P f)). Qed.
Lemma lem3480575 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term50 _89711 _89725 P f) = (term51 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3480549 _89711 _89725 P f) (@lem3480548 _89711 _89725 P f)). Qed.
Lemma lem3480576 {A : Type'} (P : type686 A) (f : type672 A) : (term52 A P f) = (term53 A P f).
Proof. exact (@lem3480575 A (A -> Prop) P f). Qed.
Lemma lem3480577 {A : Type'} (f : type686 A) (s : A -> Prop) : (term54 A f s) = (term55 A f s).
Proof. exact (@lem3480576 A (term56 A f) (term57 A s)). Qed.
Lemma lem3480578 {A : Type'} (t : A -> Prop) (f : type686 A) : (term58 A f t) = (@IN (A -> Prop) t f).
Proof. exact (eq_refl (term58 A f t)). Qed.
Lemma lem3480579 {A : Type'} (GEN_PVAR_75 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_75) = (@SETSPEC (A -> Prop) GEN_PVAR_75).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_75)). Qed.
Lemma lem3480580 {A : Type'} (GEN_PVAR_75 : A -> Prop) (t : A -> Prop) (f : type686 A) : (term59 A GEN_PVAR_75 f t) = (term60 A GEN_PVAR_75 t f).
Proof. exact (MK_COMB (@lem3480579 A GEN_PVAR_75) (@lem3480578 A t f)). Qed.
Lemma lem3480581 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (@INTER A s t).
Proof. exact (eq_refl (term61 A s t)). Qed.
Lemma lem3480582 {A : Type'} (GEN_PVAR_75 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A GEN_PVAR_75 f s t) = (term63 A GEN_PVAR_75 f s t).
Proof. exact (MK_COMB (@lem3480580 A GEN_PVAR_75 t f) (@lem3480581 A s t)). Qed.
Lemma lem3480583 {A : Type'} (GEN_PVAR_75 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term64 A GEN_PVAR_75 f s) = (term65 A GEN_PVAR_75 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480582 A GEN_PVAR_75 f s t)). Qed.
Lemma lem3480584 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3480585 {A : Type'} (GEN_PVAR_75 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term66 A GEN_PVAR_75 f s) = (term67 A GEN_PVAR_75 f s).
Proof. exact (MK_COMB (@lem3480584 A) (@lem3480583 A GEN_PVAR_75 f s)). Qed.
Lemma lem3480586 {A : Type'} (f : type686 A) (s : A -> Prop) : (term68 A f s) = (term69 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_75 : A -> Prop => @lem3480585 A GEN_PVAR_75 f s)). Qed.
Lemma lem3480587 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3480588 {A : Type'} (f : type686 A) (s : A -> Prop) : (term70 A f s) = (term71 A f s).
Proof. exact (MK_COMB (@lem3480587 A) (@lem3480586 A f s)). Qed.
Lemma lem3480589 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3480590 {A : Type'} (f : type686 A) (s : A -> Prop) : (term54 A f s) = (term7 A f s).
Proof. exact (MK_COMB (@lem3480589 A) (@lem3480588 A f s)). Qed.
Lemma lem3480591 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3480592 {A : Type'} (f : type686 A) (s : A -> Prop) : (term72 A f s) = (term73 A f s).
Proof. exact (MK_COMB (@lem3480591 A) (@lem3480590 A f s)). Qed.
Lemma lem3480593 {A : Type'} (t : A -> Prop) (f : type686 A) : (term58 A f t) = (@IN (A -> Prop) t f).
Proof. exact (eq_refl (term58 A f t)). Qed.
Lemma lem3480594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480595 {A : Type'} (t : A -> Prop) (f : type686 A) : (term74 A f t) = (term75 A t f).
Proof. exact (MK_COMB (@lem3480594) (@lem3480593 A t f)). Qed.
Lemma lem3480596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (@INTER A s t).
Proof. exact (eq_refl (term61 A s t)). Qed.
Lemma lem3480597 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem3480598 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) : (term76 A a s t) = (term77 A a s t).
Proof. exact (MK_COMB (@lem3480597 A a) (@lem3480596 A s t)). Qed.
Lemma lem3480599 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) (t : A -> Prop) : (term78 A f a s t) = (term79 A f a s t).
Proof. exact (MK_COMB (@lem3480595 A t f) (@lem3480598 A a s t)). Qed.
Lemma lem3480600 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term80 A f a s) = (term81 A f a s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480599 A f a s t)). Qed.
Lemma lem3480601 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3480602 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term82 A f a s) = (term83 A f a s).
Proof. exact (MK_COMB (@lem3480601 A) (@lem3480600 A f a s)). Qed.
Lemma lem3480603 {A : Type'} (GEN_PVAR_56 : A) : (@SETSPEC A GEN_PVAR_56) = (@SETSPEC A GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_56)). Qed.
Lemma lem3480604 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (a : A) (s : A -> Prop) : (term84 A GEN_PVAR_56 f a s) = (term85 A GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3480603 A GEN_PVAR_56) (@lem3480602 A f a s)). Qed.
Lemma lem3480605 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3480606 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) (a : A) : (term86 A GEN_PVAR_56 f s a) = (term87 A GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3480604 A GEN_PVAR_56 f a s) (@lem3480605 A a)). Qed.
Lemma lem3480607 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term88 A GEN_PVAR_56 f s) = (term89 A GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : A => @lem3480606 A GEN_PVAR_56 f s a)). Qed.
Lemma lem3480608 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3480609 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term90 A GEN_PVAR_56 f s) = (term91 A GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3480608 A) (@lem3480607 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480610 {A : Type'} (f : type686 A) (s : A -> Prop) : (term92 A f s) = (term93 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : A => @lem3480609 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480611 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3480612 {A : Type'} (f : type686 A) (s : A -> Prop) : (term55 A f s) = (term94 A f s).
Proof. exact (MK_COMB (@lem3480611 A) (@lem3480610 A f s)). Qed.
Lemma lem3480613 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term54 A f s) = (term55 A f s)) = ((term7 A f s) = (term94 A f s)).
Proof. exact (MK_COMB (@lem3480592 A f s) (@lem3480612 A f s)). Qed.
Lemma lem3480614 {A : Type'} (f : type686 A) (s : A -> Prop) : (term7 A f s) = (term94 A f s).
Proof. exact (EQ_MP (@lem3480613 A f s) (@lem3480577 A f s)). Qed.
Lemma lem3480625 {A : Type'} (s : A -> Prop) (f : type686 A) : (term45 A s f) = (term45 A s f).
Proof. exact (eq_refl (term45 A s f)). Qed.
Lemma lem3480626 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term9 A s f) = (term7 A f s)) = ((term9 A s f) = (term94 A f s)).
Proof. exact (MK_COMB (@lem3480625 A s f) (@lem3480614 A f s)). Qed.
Lemma lem3480629 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term9 A s f) = (term94 A f s)) = ((term9 A s f) = (term7 A f s)).
Proof. exact (SYM (@lem3480626 A f s)). Qed.
Lemma lem3480656 {A : Type'} : term95 A.
Proof. exact (proj1 (@lem3258568 A)). Qed.
Lemma lem3480657 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (@lem3480656 A s). Qed.
Lemma lem3480658 {A : Type'} (s : A -> Prop) : (term96 A s) = ((@INTER A (@UNIV A) s) = s).
Proof. exact (eq_refl (term96 A s)). Qed.
Lemma lem3480663 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3480664 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3480665 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@INTERS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3480664 A) (@lem3480663 A f h1)). Qed.
Lemma lem3480667 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem3480668 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@INTERS A f) = (@UNIV A).
Proof. exact (TRANS (@lem3480665 A f h1) (@lem3480667 A)). Qed.
Lemma lem3480669 {A : Type'} : (@INTER A) = (@INTER A).
Proof. exact (eq_refl (@INTER A)). Qed.
Lemma lem3480670 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term97 A f) = (@INTER A (@UNIV A)).
Proof. exact (MK_COMB (@lem3480669 A) (@lem3480668 A f h1)). Qed.
Lemma lem3480671 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3480672 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term31 A f s) = (@INTER A (@UNIV A) s).
Proof. exact (MK_COMB (@lem3480670 A f h1) (@lem3480671 A s)). Qed.
Lemma lem3480674 {A : Type'} (s : A -> Prop) : (@INTER A (@UNIV A) s) = s.
Proof. exact (EQ_MP (@lem3480658 A s) (@lem3480657 A s)). Qed.
Lemma lem3480675 {A : Type'} (s : A -> Prop) : (@INTER A (@UNIV A) s) = s.
Proof. exact (@lem3480674 A s). Qed.
Lemma lem3480676 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term31 A f s) = s.
Proof. exact (TRANS (@lem3480672 A s f h1) (@lem3480675 A s)). Qed.
Lemma lem3480677 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3480678 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term98 A f s) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem3480677 A) (@lem3480676 A s f h1)). Qed.
Lemma lem3480679 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3480680 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term31 A f s) = s) = (s = s).
Proof. exact (MK_COMB (@lem3480678 A s f h1) (@lem3480679 A s)). Qed.
Lemma lem3480682 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3480683 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3480682 (A -> Prop) x). Qed.
Lemma lem3480684 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem3480683 A s). Qed.
Lemma lem3480685 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term31 A f s) = s) = True.
Proof. exact (TRANS (@lem3480680 A s f h1) (@lem3480684 A s)). Qed.
Lemma lem3480686 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : True = ((term31 A f s) = s).
Proof. exact (SYM (@lem3480685 A s f h1)). Qed.
Lemma lem3480703 {_89711 _89725 : Type'} : term46 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3480704 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term47 _89711 _89725 P.
Proof. exact (@lem3480703 _89711 _89725 P). Qed.
Lemma lem3480705 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term47 _89711 _89725 P) = (term48 _89711 _89725 P).
Proof. exact (eq_refl (term47 _89711 _89725 P)). Qed.
Lemma lem3480706 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term48 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3480705 _89711 _89725 P) (@lem3480704 _89711 _89725 P)). Qed.
Lemma lem3480707 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term49 _89711 _89725 P f.
Proof. exact (@lem3480706 _89711 _89725 P f). Qed.
Lemma lem3480708 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term49 _89711 _89725 P f) = ((term50 _89711 _89725 P f) = (term51 _89711 _89725 P f)).
Proof. exact (eq_refl (term49 _89711 _89725 P f)). Qed.
Lemma lem3480734 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term50 _89711 _89725 P f) = (term51 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3480708 _89711 _89725 P f) (@lem3480707 _89711 _89725 P f)). Qed.
Lemma lem3480735 {A : Type'} (P : type686 A) (f : type672 A) : (term52 A P f) = (term53 A P f).
Proof. exact (@lem3480734 A (A -> Prop) P f). Qed.
Lemma lem3480736 {A : Type'} (f : type686 A) (s : A -> Prop) : (term99 A f s) = (term100 A f s).
Proof. exact (@lem3480735 A (term56 A f) (term101 A s)). Qed.
Lemma lem3480737 {A : Type'} (t : A -> Prop) (f : type686 A) : (term58 A f t) = (@IN (A -> Prop) t f).
Proof. exact (eq_refl (term58 A f t)). Qed.
Lemma lem3480738 {A : Type'} (GEN_PVAR_76 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_76) = (@SETSPEC (A -> Prop) GEN_PVAR_76).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_76)). Qed.
Lemma lem3480739 {A : Type'} (GEN_PVAR_76 : A -> Prop) (t : A -> Prop) (f : type686 A) : (term59 A GEN_PVAR_76 f t) = (term60 A GEN_PVAR_76 t f).
Proof. exact (MK_COMB (@lem3480738 A GEN_PVAR_76) (@lem3480737 A t f)). Qed.
Lemma lem3480740 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term102 A s t) = (@INTER A t s).
Proof. exact (eq_refl (term102 A s t)). Qed.
Lemma lem3480741 {A : Type'} (GEN_PVAR_76 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term103 A GEN_PVAR_76 f s t) = (term104 A GEN_PVAR_76 f t s).
Proof. exact (MK_COMB (@lem3480739 A GEN_PVAR_76 t f) (@lem3480740 A t s)). Qed.
Lemma lem3480742 {A : Type'} (GEN_PVAR_76 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term105 A GEN_PVAR_76 f s) = (term106 A GEN_PVAR_76 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480741 A GEN_PVAR_76 f t s)). Qed.
Lemma lem3480743 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3480744 {A : Type'} (GEN_PVAR_76 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term107 A GEN_PVAR_76 f s) = (term108 A GEN_PVAR_76 f s).
Proof. exact (MK_COMB (@lem3480743 A) (@lem3480742 A GEN_PVAR_76 f s)). Qed.
Lemma lem3480745 {A : Type'} (f : type686 A) (s : A -> Prop) : (term109 A f s) = (term110 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_76 : A -> Prop => @lem3480744 A GEN_PVAR_76 f s)). Qed.
Lemma lem3480746 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3480747 {A : Type'} (f : type686 A) (s : A -> Prop) : (term111 A f s) = (term112 A f s).
Proof. exact (MK_COMB (@lem3480746 A) (@lem3480745 A f s)). Qed.
Lemma lem3480748 {A : Type'} : (@INTERS A) = (@INTERS A).
Proof. exact (eq_refl (@INTERS A)). Qed.
Lemma lem3480749 {A : Type'} (f : type686 A) (s : A -> Prop) : (term99 A f s) = (term29 A f s).
Proof. exact (MK_COMB (@lem3480748 A) (@lem3480747 A f s)). Qed.
Lemma lem3480750 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3480751 {A : Type'} (f : type686 A) (s : A -> Prop) : (term113 A f s) = (term114 A f s).
Proof. exact (MK_COMB (@lem3480750 A) (@lem3480749 A f s)). Qed.
Lemma lem3480752 {A : Type'} (t : A -> Prop) (f : type686 A) : (term58 A f t) = (@IN (A -> Prop) t f).
Proof. exact (eq_refl (term58 A f t)). Qed.
Lemma lem3480753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480754 {A : Type'} (t : A -> Prop) (f : type686 A) : (term74 A f t) = (term75 A t f).
Proof. exact (MK_COMB (@lem3480753) (@lem3480752 A t f)). Qed.
Lemma lem3480755 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term102 A s t) = (@INTER A t s).
Proof. exact (eq_refl (term102 A s t)). Qed.
Lemma lem3480756 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem3480757 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) : (term115 A a s t) = (term77 A a t s).
Proof. exact (MK_COMB (@lem3480756 A a) (@lem3480755 A t s)). Qed.
Lemma lem3480758 {A : Type'} (f : type686 A) (a : A) (t : A -> Prop) (s : A -> Prop) : (term116 A f a s t) = (term117 A f a t s).
Proof. exact (MK_COMB (@lem3480754 A t f) (@lem3480757 A a t s)). Qed.
Lemma lem3480759 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term118 A f a s) = (term119 A f a s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480758 A f a t s)). Qed.
Lemma lem3480760 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3480761 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term120 A f a s) = (term121 A f a s).
Proof. exact (MK_COMB (@lem3480760 A) (@lem3480759 A f a s)). Qed.
Lemma lem3480762 {A : Type'} (GEN_PVAR_56 : A) : (@SETSPEC A GEN_PVAR_56) = (@SETSPEC A GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_56)). Qed.
Lemma lem3480763 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (a : A) (s : A -> Prop) : (term122 A GEN_PVAR_56 f a s) = (term123 A GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3480762 A GEN_PVAR_56) (@lem3480761 A f a s)). Qed.
Lemma lem3480764 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3480765 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) (a : A) : (term124 A GEN_PVAR_56 f s a) = (term125 A GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3480763 A GEN_PVAR_56 f a s) (@lem3480764 A a)). Qed.
Lemma lem3480766 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term126 A GEN_PVAR_56 f s) = (term127 A GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : A => @lem3480765 A GEN_PVAR_56 f s a)). Qed.
Lemma lem3480767 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3480768 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term128 A GEN_PVAR_56 f s) = (term129 A GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3480767 A) (@lem3480766 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480769 {A : Type'} (f : type686 A) (s : A -> Prop) : (term130 A f s) = (term131 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : A => @lem3480768 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480770 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3480771 {A : Type'} (f : type686 A) (s : A -> Prop) : (term100 A f s) = (term132 A f s).
Proof. exact (MK_COMB (@lem3480770 A) (@lem3480769 A f s)). Qed.
Lemma lem3480772 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term99 A f s) = (term100 A f s)) = ((term29 A f s) = (term132 A f s)).
Proof. exact (MK_COMB (@lem3480751 A f s) (@lem3480771 A f s)). Qed.
Lemma lem3480773 {A : Type'} (f : type686 A) (s : A -> Prop) : (term29 A f s) = (term132 A f s).
Proof. exact (EQ_MP (@lem3480772 A f s) (@lem3480736 A f s)). Qed.
Lemma lem3480784 {A : Type'} (f : type686 A) (s : A -> Prop) : (term98 A f s) = (term98 A f s).
Proof. exact (eq_refl (term98 A f s)). Qed.
Lemma lem3480785 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term31 A f s) = (term29 A f s)) = ((term31 A f s) = (term132 A f s)).
Proof. exact (MK_COMB (@lem3480784 A f s) (@lem3480773 A f s)). Qed.
Lemma lem3480788 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term31 A f s) = (term132 A f s)) = ((term31 A f s) = (term29 A f s)).
Proof. exact (SYM (@lem3480785 A f s)). Qed.
Lemma lem3480804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3480805 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term134 A s t).
Proof. exact (@lem3480804 (A -> Prop) s t). Qed.
Lemma lem3480806 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term135 A f).
Proof. exact (@lem3480805 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3480815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3480816 {A : Type'} (f : type686 A) : (term23 A f) = (term136 A f).
Proof. exact (MK_COMB (@lem3480815) (@lem3480806 A f)). Qed.
Lemma lem3480817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480818 {A : Type'} (f : type686 A) : (term10 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3480817) (@lem3480816 A f)). Qed.
Lemma lem3480822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3480823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (@lem3480822 A s t). Qed.
Lemma lem3480824 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term9 A s f) = (term94 A f s)) = (term138 A f s).
Proof. exact (@lem3480823 A (term9 A s f) (term94 A f s)). Qed.
Lemma lem3480843 {A : Type'} (f : type686 A) (s : A -> Prop) : (term139 A f s) = (term140 A f s).
Proof. exact (MK_COMB (@lem3480818 A f) (@lem3480824 A f s)). Qed.
Lemma lem3480846 {A : Type'} (f : type686 A) (s : A -> Prop) : (term140 A f s) = (term139 A f s).
Proof. exact (SYM (@lem3480843 A f s)). Qed.
Lemma lem3480856 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480857 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3480856 (A -> Prop) P x). Qed.
Lemma lem3480858 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3480857 A f x). Qed.
Lemma lem3480859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480860 {A : Type'} (f : type686 A) (x : A -> Prop) : (term141 A x f) = (term142 A f x).
Proof. exact (MK_COMB (@lem3480859) (@lem3480858 A f x)). Qed.
Lemma lem3480862 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3480863 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3480862 (A -> Prop) x). Qed.
Lemma lem3480864 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3480860 A f x) (@lem3480863 A x)). Qed.
Lemma lem3480866 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3480867 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term143 A f x).
Proof. exact (@lem3480866 (f x)). Qed.
Lemma lem3480868 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term143 A f x).
Proof. exact (TRANS (@lem3480864 A f x) (@lem3480867 A f x)). Qed.
Lemma lem3480869 {A : Type'} (f : type686 A) : (term144 A f) = (term145 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3480868 A f x)). Qed.
Lemma lem3480870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3480871 {A : Type'} (f : type686 A) : (term135 A f) = (term146 A f).
Proof. exact (MK_COMB (@lem3480870 A) (@lem3480869 A f)). Qed.
Lemma lem3480876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3480877 {A : Type'} (f : type686 A) : (term136 A f) = (term147 A f).
Proof. exact (MK_COMB (@lem3480876) (@lem3480871 A f)). Qed.
Lemma lem3480878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480879 {A : Type'} (f : type686 A) : (term137 A f) = (term148 A f).
Proof. exact (MK_COMB (@lem3480878) (@lem3480877 A f)). Qed.
Lemma lem3480887 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3480888 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (@lem3480887 A s x t). Qed.
Lemma lem3480889 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term150 A x s f) = (term151 A s x f).
Proof. exact (@lem3480888 A s x (@INTERS A f)). Qed.
Lemma lem3480893 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480894 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3480893 A P x). Qed.
Lemma lem3480895 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3480894 A s x). Qed.
Lemma lem3480896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3480897 {A : Type'} (s : A -> Prop) (x : A) : (term152 A x s) = (term153 A s x).
Proof. exact (MK_COMB (@lem3480896) (@lem3480895 A s x)). Qed.
Lemma lem3480899 {A : Type'} (s : type686 A) (x : A) : (term154 A x s) = (term155 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3480900 {A : Type'} (s : type686 A) (x : A) : (term154 A x s) = (term155 A s x).
Proof. exact (@lem3480899 A s x). Qed.
Lemma lem3480901 {A : Type'} (f : type686 A) (x : A) : (term154 A x f) = (term155 A f x).
Proof. exact (@lem3480900 A f x). Qed.
Lemma lem3480909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480910 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3480909 (A -> Prop) P x). Qed.
Lemma lem3480911 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3480910 A f t). Qed.
Lemma lem3480912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480913 {A : Type'} (f : type686 A) (t : A -> Prop) : (term75 A t f) = (term156 A f t).
Proof. exact (MK_COMB (@lem3480912) (@lem3480911 A f t)). Qed.
Lemma lem3480915 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480916 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3480915 A P x). Qed.
Lemma lem3480917 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3480916 A t x). Qed.
Lemma lem3480918 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term157 A f x t) = (term158 A f t x).
Proof. exact (MK_COMB (@lem3480913 A f t) (@lem3480917 A t x)). Qed.
Lemma lem3480921 {A : Type'} (f : type686 A) (x : A) : (term159 A f x) = (term160 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480918 A f t x)). Qed.
Lemma lem3480922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3480923 {A : Type'} (f : type686 A) (x : A) : (term155 A f x) = (term161 A f x).
Proof. exact (MK_COMB (@lem3480922 A) (@lem3480921 A f x)). Qed.
Lemma lem3480928 {A : Type'} (f : type686 A) (x : A) : (term154 A x f) = (term161 A f x).
Proof. exact (TRANS (@lem3480901 A f x) (@lem3480923 A f x)). Qed.
Lemma lem3480929 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term151 A s x f) = (term162 A s f x).
Proof. exact (MK_COMB (@lem3480897 A s x) (@lem3480928 A f x)). Qed.
Lemma lem3480932 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term150 A x s f) = (term162 A s f x).
Proof. exact (TRANS (@lem3480889 A s x f) (@lem3480929 A s f x)). Qed.
Lemma lem3480933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480934 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term163 A x s f) = (term164 A s f x).
Proof. exact (MK_COMB (@lem3480933) (@lem3480932 A s f x)). Qed.
Lemma lem3480936 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term165 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3480937 {A : Type'} (p : A -> Prop) (x : A) : (term165 A x p) = (p x).
Proof. exact (@lem3480936 A p x). Qed.
Lemma lem3480938 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term166 A x f s) = (term167 A f s x).
Proof. exact (@lem3480937 A (term168 A f s) x). Qed.
Lemma lem3480939 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term167 A f s a) = (term83 A f a s).
Proof. exact (eq_refl (term167 A f s a)). Qed.
Lemma lem3480940 {A : Type'} (GEN_PVAR_56 : A) : (@SETSPEC A GEN_PVAR_56) = (@SETSPEC A GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_56)). Qed.
Lemma lem3480941 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (a : A) (s : A -> Prop) : (term169 A GEN_PVAR_56 f s a) = (term85 A GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3480940 A GEN_PVAR_56) (@lem3480939 A f a s)). Qed.
Lemma lem3480942 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3480943 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) (a : A) : (term170 A GEN_PVAR_56 f s a) = (term87 A GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3480941 A GEN_PVAR_56 f a s) (@lem3480942 A a)). Qed.
Lemma lem3480944 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term171 A GEN_PVAR_56 f s) = (term89 A GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : A => @lem3480943 A GEN_PVAR_56 f s a)). Qed.
Lemma lem3480945 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3480946 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term172 A GEN_PVAR_56 f s) = (term91 A GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3480945 A) (@lem3480944 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480947 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term93 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : A => @lem3480946 A GEN_PVAR_56 f s)). Qed.
Lemma lem3480948 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3480949 {A : Type'} (f : type686 A) (s : A -> Prop) : (term174 A f s) = (term94 A f s).
Proof. exact (MK_COMB (@lem3480948 A) (@lem3480947 A f s)). Qed.
Lemma lem3480950 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3480951 {A : Type'} (x : A) (f : type686 A) (s : A -> Prop) : (term166 A x f s) = (term175 A x f s).
Proof. exact (MK_COMB (@lem3480950 A x) (@lem3480949 A f s)). Qed.
Lemma lem3480952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480953 {A : Type'} (x : A) (f : type686 A) (s : A -> Prop) : (term176 A x f s) = (term177 A x f s).
Proof. exact (MK_COMB (@lem3480952) (@lem3480951 A x f s)). Qed.
Lemma lem3480954 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : (term167 A f s x) = (term83 A f x s).
Proof. exact (eq_refl (term167 A f s x)). Qed.
Lemma lem3480955 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : ((term166 A x f s) = (term167 A f s x)) = ((term175 A x f s) = (term83 A f x s)).
Proof. exact (MK_COMB (@lem3480953 A x f s) (@lem3480954 A f x s)). Qed.
Lemma lem3480956 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : (term175 A x f s) = (term83 A f x s).
Proof. exact (EQ_MP (@lem3480955 A f x s) (@lem3480938 A f s x)). Qed.
Lemma lem3480964 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480965 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3480964 (A -> Prop) P x). Qed.
Lemma lem3480966 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3480965 A f t). Qed.
Lemma lem3480967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480968 {A : Type'} (f : type686 A) (t : A -> Prop) : (term75 A t f) = (term156 A f t).
Proof. exact (MK_COMB (@lem3480967) (@lem3480966 A f t)). Qed.
Lemma lem3480970 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3480971 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (@lem3480970 A s x t). Qed.
Lemma lem3480975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3480975 A P x). Qed.
Lemma lem3480977 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3480976 A s x). Qed.
Lemma lem3480978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3480979 {A : Type'} (s : A -> Prop) (x : A) : (term152 A x s) = (term153 A s x).
Proof. exact (MK_COMB (@lem3480978) (@lem3480977 A s x)). Qed.
Lemma lem3480981 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3480982 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3480981 A P x). Qed.
Lemma lem3480983 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3480982 A t x). Qed.
Lemma lem3480984 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term149 A s x t) = (term178 A s t x).
Proof. exact (MK_COMB (@lem3480979 A s x) (@lem3480983 A t x)). Qed.
Lemma lem3480987 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term77 A x s t) = (term178 A s t x).
Proof. exact (TRANS (@lem3480971 A s x t) (@lem3480984 A s t x)). Qed.
Lemma lem3480988 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term79 A f x s t) = (term179 A f s t x).
Proof. exact (MK_COMB (@lem3480968 A f t) (@lem3480987 A s t x)). Qed.
Lemma lem3480991 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term81 A f x s) = (term180 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3480988 A f s t x)). Qed.
Lemma lem3480992 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3480993 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term83 A f x s) = (term181 A f s x).
Proof. exact (MK_COMB (@lem3480992 A) (@lem3480991 A f s x)). Qed.
Lemma lem3480998 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term175 A x f s) = (term181 A f s x).
Proof. exact (TRANS (@lem3480956 A f x s) (@lem3480993 A f s x)). Qed.
Lemma lem3480999 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term150 A x s f) = (term175 A x f s)) = ((term162 A s f x) = (term181 A f s x)).
Proof. exact (MK_COMB (@lem3480934 A s f x) (@lem3480998 A f s x)). Qed.
Lemma lem3481002 {A : Type'} (f : type686 A) (s : A -> Prop) : (term182 A f s) = (term183 A f s).
Proof. exact (fun_ext (fun x : A => @lem3480999 A f s x)). Qed.
Lemma lem3481003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3481004 {A : Type'} (f : type686 A) (s : A -> Prop) : (term138 A f s) = (term184 A f s).
Proof. exact (MK_COMB (@lem3481003 A) (@lem3481002 A f s)). Qed.
Lemma lem3481009 {A : Type'} (f : type686 A) (s : A -> Prop) : (term140 A f s) = (term185 A f s).
Proof. exact (MK_COMB (@lem3480879 A f) (@lem3481004 A f s)). Qed.
Lemma lem3481012 {A : Type'} (f : type686 A) (s : A -> Prop) : (term185 A f s) = (term140 A f s).
Proof. exact (SYM (@lem3481009 A f s)). Qed.
Lemma lem3481014 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3481015 {A : Type'} (f : type686 A) (s : A -> Prop) : (term185 A f s) = (term187 A f s).
Proof. exact (@lem3481014 (term185 A f s)). Qed.
Lemma lem3481016 {A : Type'} (f : type686 A) (s : A -> Prop) : (term187 A f s) = (term185 A f s).
Proof. exact (SYM (@lem3481015 A f s)). Qed.
Lemma lem3481017 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term188 A f s) : term188 A f s.
Proof. exact (h1). Qed.
Lemma lem3481020 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term187 A f s) : term187 A f s.
Proof. exact (h1). Qed.
Lemma lem3481021 {A : Type'} (f : type686 A) (s : A -> Prop) : term189 A f s.
Proof. exact (fun h0 : term187 A f s => @lem3481020 A f s h0). Qed.
Lemma lem3481022 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term189 A f s) : term189 A f s.
Proof. exact (h1). Qed.
Lemma lem3481023 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term187 A f s) : term187 A f s.
Proof. exact (h1). Qed.
Lemma lem3481024 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term187 A f s) (h2 : term189 A f s) : term187 A f s.
Proof. exact (@lem3481022 A f s h2 (@lem3481023 A f s h1)). Qed.
Lemma lem3481025 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term187 A f s) : term190 A f s.
Proof. exact (fun h0 : term189 A f s => @lem3481024 A f s h1 h0). Qed.
Lemma lem3481026 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term189 A f s) : term189 A f s.
Proof. exact (h1). Qed.
Lemma lem3481027 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term187 A f s) (h2 : term189 A f s) : term187 A f s.
Proof. exact (@lem3481025 A f s h1 (@lem3481026 A f s h2)). Qed.
Lemma lem3481028 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term189 A f s) : term189 A f s.
Proof. exact (fun h0 : term187 A f s => @lem3481027 A f s h0 h1). Qed.
Lemma lem3481029 {A : Type'} (f : type686 A) (s : A -> Prop) : term191 A f s.
Proof. exact (fun h0 : term189 A f s => @lem3481028 A f s h0). Qed.
Lemma lem3481032 {A : Type'} (f : type686 A) (s : A -> Prop) : term189 A f s.
Proof. exact (@lem3481029 A f s (@lem3481021 A f s)). Qed.
Lemma lem3481033 {A : Type'} (f : type686 A) (s : A -> Prop) : term189 A f s.
Proof. exact (@lem3481032 A f s). Qed.
Lemma lem3481043 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3481044 {A : Type'} (f : type686 A) (s : A -> Prop) : (term187 A f s) = (term192 A f s).
Proof. exact (@lem3481043 (term188 A f s)). Qed.
Lemma lem3481046 (t : Prop) : (term193 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3481047 {A : Type'} (f : type686 A) (s : A -> Prop) : (term192 A f s) = (term185 A f s).
Proof. exact (@lem3481046 (term185 A f s)). Qed.
Lemma lem3481050 {A : Type'} (f : type686 A) (s : A -> Prop) : (term187 A f s) = (term185 A f s).
Proof. exact (TRANS (@lem3481044 A f s) (@lem3481047 A f s)). Qed.
Lemma lem3481075 {A : Type'} (s : A -> Prop) : (term194 A s) = (term195 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3481050 A f s)). Qed.
Lemma lem3481076 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3481077 {A : Type'} (s : A -> Prop) : (term196 A s) = (term197 A s).
Proof. exact (MK_COMB (@lem3481076 A) (@lem3481075 A s)). Qed.
Lemma lem3481082 {A : Type'} : (term198 A) = (term199 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3481077 A s)). Qed.
Lemma lem3481083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481092 {A : Type'} : (term200 A) = (term201 A).
Proof. exact (MK_COMB (@lem3481083 A) (@lem3481082 A)). Qed.
Lemma lem3481101 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term179 A f s t x) = (term179 A f s t x).
Proof. exact (eq_refl (term179 A f s t x)). Qed.
Lemma lem3481102 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term180 A f s x) = (term180 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481101 A f s t x)). Qed.
Lemma lem3481103 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481104 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term181 A f s x) = (term181 A f s x).
Proof. exact (MK_COMB (@lem3481103 A) (@lem3481102 A f s x)). Qed.
Lemma lem3481109 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term158 A f t x) = (term158 A f t x).
Proof. exact (eq_refl (term158 A f t x)). Qed.
Lemma lem3481110 {A : Type'} (f : type686 A) (x : A) : (term160 A f x) = (term160 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481109 A f t x)). Qed.
Lemma lem3481111 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481112 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term161 A f x).
Proof. exact (MK_COMB (@lem3481111 A) (@lem3481110 A f x)). Qed.
Lemma lem3481115 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term153 A s x).
Proof. exact (eq_refl (term153 A s x)). Qed.
Lemma lem3481116 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term162 A s f x) = (term162 A s f x).
Proof. exact (MK_COMB (@lem3481115 A s x) (@lem3481112 A f x)). Qed.
Lemma lem3481117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481118 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term164 A s f x) = (term164 A s f x).
Proof. exact (MK_COMB (@lem3481117) (@lem3481116 A s f x)). Qed.
Lemma lem3481119 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term162 A s f x) = (term181 A f s x)) = ((term162 A s f x) = (term181 A f s x)).
Proof. exact (MK_COMB (@lem3481118 A s f x) (@lem3481104 A f s x)). Qed.
Lemma lem3481120 {A : Type'} (f : type686 A) (s : A -> Prop) : (term183 A f s) = (term183 A f s).
Proof. exact (fun_ext (fun x : A => @lem3481119 A f s x)). Qed.
Lemma lem3481121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3481122 {A : Type'} (f : type686 A) (s : A -> Prop) : (term184 A f s) = (term184 A f s).
Proof. exact (MK_COMB (@lem3481121 A) (@lem3481120 A f s)). Qed.
Lemma lem3481125 {A : Type'} (f : type686 A) (x : A -> Prop) : (term143 A f x) = (term143 A f x).
Proof. exact (eq_refl (term143 A f x)). Qed.
Lemma lem3481126 {A : Type'} (f : type686 A) : (term145 A f) = (term145 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3481125 A f x)). Qed.
Lemma lem3481127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481128 {A : Type'} (f : type686 A) : (term146 A f) = (term146 A f).
Proof. exact (MK_COMB (@lem3481127 A) (@lem3481126 A f)). Qed.
Lemma lem3481129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481130 {A : Type'} (f : type686 A) : (term147 A f) = (term147 A f).
Proof. exact (MK_COMB (@lem3481129) (@lem3481128 A f)). Qed.
Lemma lem3481131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3481132 {A : Type'} (f : type686 A) : (term148 A f) = (term148 A f).
Proof. exact (MK_COMB (@lem3481131) (@lem3481130 A f)). Qed.
Lemma lem3481133 {A : Type'} (f : type686 A) (s : A -> Prop) : (term185 A f s) = (term185 A f s).
Proof. exact (MK_COMB (@lem3481132 A f) (@lem3481122 A f s)). Qed.
Lemma lem3481134 {A : Type'} (s : A -> Prop) : (term195 A s) = (term195 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3481133 A f s)). Qed.
Lemma lem3481135 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3481136 {A : Type'} (s : A -> Prop) : (term197 A s) = (term197 A s).
Proof. exact (MK_COMB (@lem3481135 A) (@lem3481134 A s)). Qed.
Lemma lem3481137 {A : Type'} : (term199 A) = (term199 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3481136 A s)). Qed.
Lemma lem3481138 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481139 {A : Type'} : (term201 A) = (term201 A).
Proof. exact (MK_COMB (@lem3481138 A) (@lem3481137 A)). Qed.
Lemma lem3481188 {A : Type'} : (term200 A) = (term201 A).
Proof. exact (TRANS (@lem3481092 A) (@lem3481139 A)). Qed.
Lemma lem3481189 {A : Type'} : (term201 A) = (term200 A).
Proof. exact (SYM (@lem3481188 A)). Qed.
Lemma lem3481190 {A : Type'} (f : type686 A) (h1 : term147 A f) : term147 A f.
Proof. exact (h1). Qed.
Lemma lem3481192 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3481193 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term162 A s f x) = (term181 A f s x)) = (term202 A f s x).
Proof. exact (@lem3481192 ((term162 A s f x) = (term181 A f s x))). Qed.
Lemma lem3481194 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term202 A f s x) = ((term162 A s f x) = (term181 A f s x)).
Proof. exact (SYM (@lem3481193 A f s x)). Qed.
Lemma lem3481195 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term203 A f s x) : term203 A f s x.
Proof. exact (h1). Qed.
Lemma lem3481198 {A : Type'} (f : type686 A) (x : A -> Prop) : (term204 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3481199 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3481200 {A : Type'} (f : type686 A) : (term147 A f) = (term207 A f).
Proof. exact (@lem3481199 A (term145 A f)). Qed.
Lemma lem3481201 {A : Type'} (f : type686 A) (x : A -> Prop) : (term208 A f x) = (term143 A f x).
Proof. exact (eq_refl (term208 A f x)). Qed.
Lemma lem3481202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481203 {A : Type'} (f : type686 A) (x : A -> Prop) : (term209 A f x) = (term204 A f x).
Proof. exact (MK_COMB (@lem3481202) (@lem3481201 A f x)). Qed.
Lemma lem3481204 {A : Type'} (f : type686 A) (x : A -> Prop) : (term209 A f x) = (f x).
Proof. exact (TRANS (@lem3481203 A f x) (@lem3481198 A f x)). Qed.
Lemma lem3481205 {A : Type'} (f : type686 A) : (term210 A f) = (term211 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3481204 A f x)). Qed.
Lemma lem3481206 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481207 {A : Type'} (f : type686 A) : (term207 A f) = (term212 A f).
Proof. exact (MK_COMB (@lem3481206 A) (@lem3481205 A f)). Qed.
Lemma lem3481216 {A : Type'} (f : type686 A) : (term147 A f) = (term212 A f).
Proof. exact (TRANS (@lem3481200 A f) (@lem3481207 A f)). Qed.
Lemma lem3481217 {A : Type'} (f : type686 A) (h1 : term147 A f) : term212 A f.
Proof. exact (EQ_MP (@lem3481216 A f) (@lem3481190 A f h1)). Qed.
Lemma lem3481228 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term213 A f t x) = (term214 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3481233 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term158 A f t x) = (term215 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3481234 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3481235 {A : Type'} (f : type686 A) (x : A) : (term216 A f x) = (term217 A f x).
Proof. exact (@lem3481234 A (term160 A f x)). Qed.
Lemma lem3481236 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term218 A f x t) = (term158 A f t x).
Proof. exact (eq_refl (term218 A f x t)). Qed.
Lemma lem3481237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481238 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term219 A f x t) = (term213 A f t x).
Proof. exact (MK_COMB (@lem3481237) (@lem3481236 A f t x)). Qed.
Lemma lem3481239 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term219 A f x t) = (term214 A f t x).
Proof. exact (TRANS (@lem3481238 A f t x) (@lem3481228 A f t x)). Qed.
Lemma lem3481240 {A : Type'} (f : type686 A) (x : A) : (term220 A f x) = (term221 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481239 A f t x)). Qed.
Lemma lem3481241 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481242 {A : Type'} (f : type686 A) (x : A) : (term217 A f x) = (term222 A f x).
Proof. exact (MK_COMB (@lem3481241 A) (@lem3481240 A f x)). Qed.
Lemma lem3481243 {A : Type'} (f : type686 A) (x : A) : (term216 A f x) = (term222 A f x).
Proof. exact (TRANS (@lem3481235 A f x) (@lem3481242 A f x)). Qed.
Lemma lem3481244 {A : Type'} (f : type686 A) (x : A) : (term160 A f x) = (term223 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481233 A f t x)). Qed.
Lemma lem3481245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481246 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term224 A f x).
Proof. exact (MK_COMB (@lem3481245 A) (@lem3481244 A f x)). Qed.
Lemma lem3481248 {A : Type'} (s : A -> Prop) (x : A) : (term225 A s x) = (term225 A s x).
Proof. exact (eq_refl (term225 A s x)). Qed.
Lemma lem3481249 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term226 A s f x) = (term227 A s f x).
Proof. exact (MK_COMB (@lem3481248 A s x) (@lem3481243 A f x)). Qed.
Lemma lem3481250 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term228 A s f x) = (term226 A s f x).
Proof. exact (@lem17045 (s x) (term161 A f x)). Qed.
Lemma lem3481251 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term228 A s f x) = (term227 A s f x).
Proof. exact (TRANS (@lem3481250 A s f x) (@lem3481249 A s f x)). Qed.
Lemma lem3481253 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term153 A s x).
Proof. exact (eq_refl (term153 A s x)). Qed.
Lemma lem3481254 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term162 A s f x) = (term229 A s f x).
Proof. exact (MK_COMB (@lem3481253 A s x) (@lem3481246 A f x)). Qed.
Lemma lem3481265 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term230 A s t x) = (term231 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3481270 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term232 A f t).
Proof. exact (eq_refl (term232 A f t)). Qed.
Lemma lem3481271 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term233 A f s t x) = (term234 A f s t x).
Proof. exact (MK_COMB (@lem3481270 A f t) (@lem3481265 A s t x)). Qed.
Lemma lem3481272 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term235 A f s t x) = (term233 A f s t x).
Proof. exact (@lem17362 (f t) (term178 A s t x)). Qed.
Lemma lem3481273 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term235 A f s t x) = (term234 A f s t x).
Proof. exact (TRANS (@lem3481272 A f s t x) (@lem3481271 A f s t x)). Qed.
Lemma lem3481278 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term179 A f s t x) = (term236 A f s t x).
Proof. exact (@lem17265 (f t) (term178 A s t x)). Qed.
Lemma lem3481279 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3481280 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term237 A f s x) = (term238 A f s x).
Proof. exact (@lem3481279 A (term180 A f s x)). Qed.
Lemma lem3481281 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term239 A f s x t) = (term179 A f s t x).
Proof. exact (eq_refl (term239 A f s x t)). Qed.
Lemma lem3481282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481283 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term240 A f s x t) = (term235 A f s t x).
Proof. exact (MK_COMB (@lem3481282) (@lem3481281 A f s t x)). Qed.
Lemma lem3481284 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term240 A f s x t) = (term234 A f s t x).
Proof. exact (TRANS (@lem3481283 A f s t x) (@lem3481273 A f s t x)). Qed.
Lemma lem3481285 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term241 A f s x) = (term242 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481284 A f s t x)). Qed.
Lemma lem3481286 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481287 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term238 A f s x) = (term243 A f s x).
Proof. exact (MK_COMB (@lem3481286 A) (@lem3481285 A f s x)). Qed.
Lemma lem3481288 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term237 A f s x) = (term243 A f s x).
Proof. exact (TRANS (@lem3481280 A f s x) (@lem3481287 A f s x)). Qed.
Lemma lem3481289 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term180 A f s x) = (term244 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481278 A f s t x)). Qed.
Lemma lem3481290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481291 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term181 A f s x) = (term245 A f s x).
Proof. exact (MK_COMB (@lem3481290 A) (@lem3481289 A f s x)). Qed.
Lemma lem3481292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481293 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term246 A s f x) = (term247 A s f x).
Proof. exact (MK_COMB (@lem3481292) (@lem3481251 A s f x)). Qed.
Lemma lem3481294 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term248 A f s x) = (term249 A f s x).
Proof. exact (MK_COMB (@lem3481293 A s f x) (@lem3481291 A f s x)). Qed.
Lemma lem3481295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481296 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term250 A s f x) = (term251 A s f x).
Proof. exact (MK_COMB (@lem3481295) (@lem3481254 A s f x)). Qed.
Lemma lem3481297 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term252 A f s x) = (term253 A f s x).
Proof. exact (MK_COMB (@lem3481296 A s f x) (@lem3481288 A f s x)). Qed.
Lemma lem3481298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481299 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term254 A f s x) = (term255 A f s x).
Proof. exact (MK_COMB (@lem3481298) (@lem3481297 A f s x)). Qed.
Lemma lem3481300 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term256 A f s x) = (term257 A f s x).
Proof. exact (MK_COMB (@lem3481299 A f s x) (@lem3481294 A f s x)). Qed.
Lemma lem3481301 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term203 A f s x) = (term256 A f s x).
Proof. exact (@lem17646 (term162 A s f x) (term181 A f s x)). Qed.
Lemma lem3481302 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term203 A f s x) = (term257 A f s x).
Proof. exact (TRANS (@lem3481301 A f s x) (@lem3481300 A f s x)). Qed.
Lemma lem3481457 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3481458 {A : Type'} (P : Prop) (Q : type686 A) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem3481457 (A -> Prop) P Q). Qed.
Lemma lem3481459 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term262 A f s x) = (term263 A f s x).
Proof. exact (@lem3481458 A (term229 A s f x) (term242 A f s x)). Qed.
Lemma lem3481460 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term264 A f s x t) = (term234 A f s t x).
Proof. exact (eq_refl (term264 A f s x t)). Qed.
Lemma lem3481461 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term265 A f s x) = (term242 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481460 A f s t x)). Qed.
Lemma lem3481462 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481463 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term266 A f s x) = (term243 A f s x).
Proof. exact (MK_COMB (@lem3481462 A) (@lem3481461 A f s x)). Qed.
Lemma lem3481464 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term251 A s f x) = (term251 A s f x).
Proof. exact (eq_refl (term251 A s f x)). Qed.
Lemma lem3481465 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term262 A f s x) = (term253 A f s x).
Proof. exact (MK_COMB (@lem3481464 A s f x) (@lem3481463 A f s x)). Qed.
Lemma lem3481466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481467 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term267 A f s x) = (term268 A f s x).
Proof. exact (MK_COMB (@lem3481466) (@lem3481465 A f s x)). Qed.
Lemma lem3481468 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term264 A f s x t) = (term234 A f s t x).
Proof. exact (eq_refl (term264 A f s x t)). Qed.
Lemma lem3481469 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term251 A s f x) = (term251 A s f x).
Proof. exact (eq_refl (term251 A s f x)). Qed.
Lemma lem3481470 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term269 A f s x t) = (term270 A f s t x).
Proof. exact (MK_COMB (@lem3481469 A s f x) (@lem3481468 A f s t x)). Qed.
Lemma lem3481471 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term271 A f s x) = (term272 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481470 A f s t x)). Qed.
Lemma lem3481472 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481473 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term263 A f s x) = (term273 A f s x).
Proof. exact (MK_COMB (@lem3481472 A) (@lem3481471 A f s x)). Qed.
Lemma lem3481474 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term262 A f s x) = (term263 A f s x)) = ((term253 A f s x) = (term273 A f s x)).
Proof. exact (MK_COMB (@lem3481467 A f s x) (@lem3481473 A f s x)). Qed.
Lemma lem3481475 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term253 A f s x) = (term273 A f s x).
Proof. exact (EQ_MP (@lem3481474 A f s x) (@lem3481459 A f s x)). Qed.
Lemma lem3481476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481477 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term255 A f s x) = (term274 A f s x).
Proof. exact (MK_COMB (@lem3481476) (@lem3481475 A f s x)). Qed.
Lemma lem3481479 {A : Type'} (P : Prop) (Q : A -> Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3481480 {A : Type'} (P : Prop) (Q : type686 A) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem3481479 (A -> Prop) P Q). Qed.
Lemma lem3481481 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term279 A s f x) = (term280 A s f x).
Proof. exact (@lem3481480 A (term281 A s x) (term221 A f x)). Qed.
Lemma lem3481482 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term282 A f x t) = (term214 A f t x).
Proof. exact (eq_refl (term282 A f x t)). Qed.
Lemma lem3481483 {A : Type'} (f : type686 A) (x : A) : (term283 A f x) = (term221 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481482 A f t x)). Qed.
Lemma lem3481484 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481485 {A : Type'} (f : type686 A) (x : A) : (term284 A f x) = (term222 A f x).
Proof. exact (MK_COMB (@lem3481484 A) (@lem3481483 A f x)). Qed.
Lemma lem3481486 {A : Type'} (s : A -> Prop) (x : A) : (term225 A s x) = (term225 A s x).
Proof. exact (eq_refl (term225 A s x)). Qed.
Lemma lem3481487 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term279 A s f x) = (term227 A s f x).
Proof. exact (MK_COMB (@lem3481486 A s x) (@lem3481485 A f x)). Qed.
Lemma lem3481488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481489 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term285 A s f x) = (term286 A s f x).
Proof. exact (MK_COMB (@lem3481488) (@lem3481487 A s f x)). Qed.
Lemma lem3481490 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term282 A f x t) = (term214 A f t x).
Proof. exact (eq_refl (term282 A f x t)). Qed.
Lemma lem3481491 {A : Type'} (s : A -> Prop) (x : A) : (term225 A s x) = (term225 A s x).
Proof. exact (eq_refl (term225 A s x)). Qed.
Lemma lem3481492 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term287 A s f x t) = (term288 A s f t x).
Proof. exact (MK_COMB (@lem3481491 A s x) (@lem3481490 A f t x)). Qed.
Lemma lem3481493 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term289 A s f x) = (term290 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481492 A s f t x)). Qed.
Lemma lem3481494 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481495 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term280 A s f x) = (term291 A s f x).
Proof. exact (MK_COMB (@lem3481494 A) (@lem3481493 A s f x)). Qed.
Lemma lem3481496 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term279 A s f x) = (term280 A s f x)) = ((term227 A s f x) = (term291 A s f x)).
Proof. exact (MK_COMB (@lem3481489 A s f x) (@lem3481495 A s f x)). Qed.
Lemma lem3481497 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term227 A s f x) = (term291 A s f x).
Proof. exact (EQ_MP (@lem3481496 A s f x) (@lem3481481 A s f x)). Qed.
Lemma lem3481498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481499 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term247 A s f x) = (term292 A s f x).
Proof. exact (MK_COMB (@lem3481498) (@lem3481497 A s f x)). Qed.
Lemma lem3481500 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term245 A f s x) = (term245 A f s x).
Proof. exact (eq_refl (term245 A f s x)). Qed.
Lemma lem3481501 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term249 A f s x) = (term293 A f s x).
Proof. exact (MK_COMB (@lem3481499 A s f x) (@lem3481500 A f s x)). Qed.
Lemma lem3481503 {A : Type'} (P : A -> Prop) (Q : Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3481504 {A : Type'} (P : type686 A) (Q : Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem3481503 (A -> Prop) P Q). Qed.
Lemma lem3481505 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term298 A f s x) = (term299 A f s x).
Proof. exact (@lem3481504 A (term290 A s f x) (term245 A f s x)). Qed.
Lemma lem3481506 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term300 A s f x t) = (term288 A s f t x).
Proof. exact (eq_refl (term300 A s f x t)). Qed.
Lemma lem3481507 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term301 A s f x) = (term290 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481506 A s f t x)). Qed.
Lemma lem3481508 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481509 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term302 A s f x) = (term291 A s f x).
Proof. exact (MK_COMB (@lem3481508 A) (@lem3481507 A s f x)). Qed.
Lemma lem3481510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481511 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term303 A s f x) = (term292 A s f x).
Proof. exact (MK_COMB (@lem3481510) (@lem3481509 A s f x)). Qed.
Lemma lem3481512 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term245 A f s x) = (term245 A f s x).
Proof. exact (eq_refl (term245 A f s x)). Qed.
Lemma lem3481513 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term298 A f s x) = (term293 A f s x).
Proof. exact (MK_COMB (@lem3481511 A s f x) (@lem3481512 A f s x)). Qed.
Lemma lem3481514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481515 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term304 A f s x) = (term305 A f s x).
Proof. exact (MK_COMB (@lem3481514) (@lem3481513 A f s x)). Qed.
Lemma lem3481516 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term300 A s f x t) = (term288 A s f t x).
Proof. exact (eq_refl (term300 A s f x t)). Qed.
Lemma lem3481517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481518 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term306 A s f x t) = (term307 A s f t x).
Proof. exact (MK_COMB (@lem3481517) (@lem3481516 A s f t x)). Qed.
Lemma lem3481519 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term245 A f s x) = (term245 A f s x).
Proof. exact (eq_refl (term245 A f s x)). Qed.
Lemma lem3481520 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term308 A t f s x) = (term309 A t f s x).
Proof. exact (MK_COMB (@lem3481518 A s f t x) (@lem3481519 A f s x)). Qed.
Lemma lem3481521 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term310 A f s x) = (term311 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481520 A t f s x)). Qed.
Lemma lem3481522 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481523 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term299 A f s x) = (term312 A f s x).
Proof. exact (MK_COMB (@lem3481522 A) (@lem3481521 A f s x)). Qed.
Lemma lem3481524 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term298 A f s x) = (term299 A f s x)) = ((term293 A f s x) = (term312 A f s x)).
Proof. exact (MK_COMB (@lem3481515 A f s x) (@lem3481523 A f s x)). Qed.
Lemma lem3481525 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term293 A f s x) = (term312 A f s x).
Proof. exact (EQ_MP (@lem3481524 A f s x) (@lem3481505 A f s x)). Qed.
Lemma lem3481526 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term249 A f s x) = (term312 A f s x).
Proof. exact (TRANS (@lem3481501 A f s x) (@lem3481525 A f s x)). Qed.
Lemma lem3481527 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term257 A f s x) = (term313 A f s x).
Proof. exact (MK_COMB (@lem3481477 A f s x) (@lem3481526 A f s x)). Qed.
Lemma lem3481529 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3481530 {A : Type'} (P : type686 A) (Q : type686 A) : (term316 A P Q) = (term317 A P Q).
Proof. exact (@lem3481529 (A -> Prop) P Q). Qed.
Lemma lem3481531 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term318 A f s x) = (term319 A f s x).
Proof. exact (@lem3481530 A (term272 A f s x) (term311 A f s x)). Qed.
Lemma lem3481532 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term320 A f s x t) = (term270 A f s t x).
Proof. exact (eq_refl (term320 A f s x t)). Qed.
Lemma lem3481533 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term321 A f s x) = (term272 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481532 A f s t x)). Qed.
Lemma lem3481534 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481535 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term322 A f s x) = (term273 A f s x).
Proof. exact (MK_COMB (@lem3481534 A) (@lem3481533 A f s x)). Qed.
Lemma lem3481536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481537 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term323 A f s x) = (term274 A f s x).
Proof. exact (MK_COMB (@lem3481536) (@lem3481535 A f s x)). Qed.
Lemma lem3481538 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term324 A f s x t) = (term309 A t f s x).
Proof. exact (eq_refl (term324 A f s x t)). Qed.
Lemma lem3481539 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term325 A f s x) = (term311 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481538 A t f s x)). Qed.
Lemma lem3481540 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481541 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term326 A f s x) = (term312 A f s x).
Proof. exact (MK_COMB (@lem3481540 A) (@lem3481539 A f s x)). Qed.
Lemma lem3481542 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term318 A f s x) = (term313 A f s x).
Proof. exact (MK_COMB (@lem3481537 A f s x) (@lem3481541 A f s x)). Qed.
Lemma lem3481543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481544 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term327 A f s x) = (term328 A f s x).
Proof. exact (MK_COMB (@lem3481543) (@lem3481542 A f s x)). Qed.
Lemma lem3481545 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term320 A f s x t) = (term270 A f s t x).
Proof. exact (eq_refl (term320 A f s x t)). Qed.
Lemma lem3481546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481547 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term329 A f s x t) = (term330 A f s t x).
Proof. exact (MK_COMB (@lem3481546) (@lem3481545 A f s t x)). Qed.
Lemma lem3481548 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term324 A f s x t) = (term309 A t f s x).
Proof. exact (eq_refl (term324 A f s x t)). Qed.
Lemma lem3481549 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term331 A f s x t) = (term332 A t f s x).
Proof. exact (MK_COMB (@lem3481547 A f s t x) (@lem3481548 A t f s x)). Qed.
Lemma lem3481550 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term333 A f s x) = (term334 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481549 A t f s x)). Qed.
Lemma lem3481551 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3481552 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term319 A f s x) = (term335 A f s x).
Proof. exact (MK_COMB (@lem3481551 A) (@lem3481550 A f s x)). Qed.
Lemma lem3481553 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term318 A f s x) = (term319 A f s x)) = ((term313 A f s x) = (term335 A f s x)).
Proof. exact (MK_COMB (@lem3481544 A f s x) (@lem3481552 A f s x)). Qed.
Lemma lem3481554 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term313 A f s x) = (term335 A f s x).
Proof. exact (EQ_MP (@lem3481553 A f s x) (@lem3481531 A f s x)). Qed.
Lemma lem3481556 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term257 A f s x) = (term335 A f s x).
Proof. exact (TRANS (@lem3481527 A f s x) (@lem3481554 A f s x)). Qed.
Lemma lem3481557 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term203 A f s x) = (term335 A f s x).
Proof. exact (TRANS (@lem3481302 A f s x) (@lem3481556 A f s x)). Qed.
Lemma lem3481558 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term203 A f s x) : term335 A f s x.
Proof. exact (EQ_MP (@lem3481557 A f s x) (@lem3481195 A f s x h1)). Qed.
Lemma lem3481559 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term332 A t f s x) : term332 A t f s x.
Proof. exact (h1). Qed.
Lemma lem3481560 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : f x'.
Proof. exact (h1). Qed.
Lemma lem3481565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481566 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481565 A Prop f x). Qed.
Lemma lem3481568 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3481566 A t x). Qed.
Lemma lem3481573 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481574 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481573 A Prop f x). Qed.
Lemma lem3481576 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3481574 A s x). Qed.
Lemma lem3481577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481578 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term336 A s x).
Proof. exact (MK_COMB (@lem3481577) (@lem3481576 A s x)). Qed.
Lemma lem3481579 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term178 A s t x) = (term337 A s t x).
Proof. exact (MK_COMB (@lem3481578 A s x) (@lem3481568 A t x)). Qed.
Lemma lem3481580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481585 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481586 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3481585 (A -> Prop) Prop f x). Qed.
Lemma lem3481588 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3481586 A f t). Qed.
Lemma lem3481589 {A : Type'} (f : type686 A) (t : A -> Prop) : (term143 A f t) = (term338 A f t).
Proof. exact (MK_COMB (@lem3481580) (@lem3481588 A f t)). Qed.
Lemma lem3481590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481591 {A : Type'} (f : type686 A) (t : A -> Prop) : (term339 A f t) = (term340 A f t).
Proof. exact (MK_COMB (@lem3481590) (@lem3481589 A f t)). Qed.
Lemma lem3481592 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term236 A f s t x) = (term341 A f s t x).
Proof. exact (MK_COMB (@lem3481591 A f t) (@lem3481579 A s t x)). Qed.
Lemma lem3481593 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term244 A f s x) = (term342 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481592 A f s t x)). Qed.
Lemma lem3481594 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481595 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term245 A f s x) = (term343 A f s x).
Proof. exact (MK_COMB (@lem3481594 A) (@lem3481593 A f s x)). Qed.
Lemma lem3481596 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481601 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481602 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481601 A Prop f x). Qed.
Lemma lem3481604 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3481602 A t x). Qed.
Lemma lem3481605 {A : Type'} (t : A -> Prop) (x : A) : (term281 A t x) = (term344 A t x).
Proof. exact (MK_COMB (@lem3481596) (@lem3481604 A t x)). Qed.
Lemma lem3481610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481611 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3481610 (A -> Prop) Prop f x). Qed.
Lemma lem3481613 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3481611 A f t). Qed.
Lemma lem3481614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481615 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term345 A f t).
Proof. exact (MK_COMB (@lem3481614) (@lem3481613 A f t)). Qed.
Lemma lem3481616 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term214 A f t x) = (term346 A f t x).
Proof. exact (MK_COMB (@lem3481615 A f t) (@lem3481605 A t x)). Qed.
Lemma lem3481617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481622 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481623 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481622 A Prop f x). Qed.
Lemma lem3481625 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3481623 A s x). Qed.
Lemma lem3481626 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3481617) (@lem3481625 A s x)). Qed.
Lemma lem3481627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481628 {A : Type'} (s : A -> Prop) (x : A) : (term225 A s x) = (term347 A s x).
Proof. exact (MK_COMB (@lem3481627) (@lem3481626 A s x)). Qed.
Lemma lem3481629 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term288 A s f t x) = (term348 A s f t x).
Proof. exact (MK_COMB (@lem3481628 A s x) (@lem3481616 A f t x)). Qed.
Lemma lem3481630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481631 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term307 A s f t x) = (term349 A s f t x).
Proof. exact (MK_COMB (@lem3481630) (@lem3481629 A s f t x)). Qed.
Lemma lem3481632 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term309 A t f s x) = (term350 A t f s x).
Proof. exact (MK_COMB (@lem3481631 A s f t x) (@lem3481595 A f s x)). Qed.
Lemma lem3481633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481639 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481638 A Prop f x). Qed.
Lemma lem3481641 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3481639 A t x). Qed.
Lemma lem3481642 {A : Type'} (t : A -> Prop) (x : A) : (term281 A t x) = (term344 A t x).
Proof. exact (MK_COMB (@lem3481633) (@lem3481641 A t x)). Qed.
Lemma lem3481643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481649 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481648 A Prop f x). Qed.
Lemma lem3481651 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3481649 A s x). Qed.
Lemma lem3481652 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3481643) (@lem3481651 A s x)). Qed.
Lemma lem3481653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481654 {A : Type'} (s : A -> Prop) (x : A) : (term225 A s x) = (term347 A s x).
Proof. exact (MK_COMB (@lem3481653) (@lem3481652 A s x)). Qed.
Lemma lem3481655 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term231 A s t x) = (term351 A s t x).
Proof. exact (MK_COMB (@lem3481654 A s x) (@lem3481642 A t x)). Qed.
Lemma lem3481660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481661 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3481660 (A -> Prop) Prop f x). Qed.
Lemma lem3481663 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3481661 A f t). Qed.
Lemma lem3481664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481665 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term345 A f t).
Proof. exact (MK_COMB (@lem3481664) (@lem3481663 A f t)). Qed.
Lemma lem3481666 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term234 A f s t x) = (term352 A f s t x).
Proof. exact (MK_COMB (@lem3481665 A f t) (@lem3481655 A s t x)). Qed.
Lemma lem3481671 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481672 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481671 A Prop f x). Qed.
Lemma lem3481674 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3481672 A t x). Qed.
Lemma lem3481675 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3481680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481681 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3481680 (A -> Prop) Prop f x). Qed.
Lemma lem3481683 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3481681 A f t). Qed.
Lemma lem3481684 {A : Type'} (f : type686 A) (t : A -> Prop) : (term143 A f t) = (term338 A f t).
Proof. exact (MK_COMB (@lem3481675) (@lem3481683 A f t)). Qed.
Lemma lem3481685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481686 {A : Type'} (f : type686 A) (t : A -> Prop) : (term339 A f t) = (term340 A f t).
Proof. exact (MK_COMB (@lem3481685) (@lem3481684 A f t)). Qed.
Lemma lem3481687 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term215 A f t x) = (term353 A f t x).
Proof. exact (MK_COMB (@lem3481686 A f t) (@lem3481674 A t x)). Qed.
Lemma lem3481688 {A : Type'} (f : type686 A) (x : A) : (term223 A f x) = (term354 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481687 A f t x)). Qed.
Lemma lem3481689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481690 {A : Type'} (f : type686 A) (x : A) : (term224 A f x) = (term355 A f x).
Proof. exact (MK_COMB (@lem3481689 A) (@lem3481688 A f x)). Qed.
Lemma lem3481695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481696 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3481695 A Prop f x). Qed.
Lemma lem3481698 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3481696 A s x). Qed.
Lemma lem3481699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481700 {A : Type'} (s : A -> Prop) (x : A) : (term153 A s x) = (term336 A s x).
Proof. exact (MK_COMB (@lem3481699) (@lem3481698 A s x)). Qed.
Lemma lem3481701 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term229 A s f x) = (term356 A s f x).
Proof. exact (MK_COMB (@lem3481700 A s x) (@lem3481690 A f x)). Qed.
Lemma lem3481702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3481703 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term251 A s f x) = (term357 A s f x).
Proof. exact (MK_COMB (@lem3481702) (@lem3481701 A s f x)). Qed.
Lemma lem3481704 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term270 A f s t x) = (term358 A f s t x).
Proof. exact (MK_COMB (@lem3481703 A s f x) (@lem3481666 A f s t x)). Qed.
Lemma lem3481705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3481706 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term330 A f s t x) = (term359 A f s t x).
Proof. exact (MK_COMB (@lem3481705) (@lem3481704 A f s t x)). Qed.
Lemma lem3481707 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term332 A t f s x) = (term360 A t f s x).
Proof. exact (MK_COMB (@lem3481706 A f s t x) (@lem3481632 A t f s x)). Qed.
Lemma lem3481708 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term332 A t f s x) : term360 A t f s x.
Proof. exact (EQ_MP (@lem3481707 A t f s x) (@lem3481559 A t f s x h1)). Qed.
Lemma lem3481713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3481714 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3481713 (A -> Prop) Prop f x). Qed.
Lemma lem3481716 {A : Type'} (f : type686 A) (x' : A -> Prop) : (f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3481714 A f x'). Qed.
Lemma lem3481718 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term358 A f s t x.
Proof. exact (h1). Qed.
Lemma lem3481719 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term350 A t f s x.
Proof. exact (h1). Qed.
Lemma lem3481720 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term352 A f s t x.
Proof. exact (proj2 (@lem3481718 A f s t x h1)). Qed.
Lemma lem3481721 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term356 A s f x.
Proof. exact (proj1 (@lem3481718 A f s t x h1)). Qed.
Lemma lem3481722 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term351 A s t x.
Proof. exact (proj2 (@lem3481720 A f s t x h1)). Qed.
Lemma lem3481724 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term355 A f x.
Proof. exact (proj2 (@lem3481721 A f s t x h1)). Qed.
Lemma lem3481728 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term343 A f s x.
Proof. exact (proj2 (@lem3481719 A t f s x h1)). Qed.
Lemma lem3481729 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term348 A s f t x.
Proof. exact (proj1 (@lem3481719 A t f s x h1)). Qed.
Lemma lem3481731 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term346 A f t x.
Proof. exact (h1). Qed.
Lemma lem3481762 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3481782 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term353 A f t x) = (term353 A f t x).
Proof. exact (eq_refl (term353 A f t x)). Qed.
Lemma lem3481783 {A : Type'} (f : type686 A) (x : A) : (term354 A f x) = (term354 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481782 A f t x)). Qed.
Lemma lem3481784 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481786 {A : Type'} (f : type686 A) (x : A) : (term355 A f x) = (term355 A f x).
Proof. exact (MK_COMB (@lem3481784 A) (@lem3481783 A f x)). Qed.
Lemma lem3481787 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term355 A f x.
Proof. exact (EQ_MP (@lem3481786 A f x) (@lem3481724 A f s t x h1)). Qed.
Lemma lem3481791 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term344 A t x.
Proof. exact (h1). Qed.
Lemma lem3481813 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term341 A f s t x) = (term361 A s f t x).
Proof. exact (@lem19490 (@I (A -> Prop) s x) (term338 A f t) (@I (A -> Prop) t x)). Qed.
Lemma lem3481814 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term342 A f s x) = (term362 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481813 A s f t x)). Qed.
Lemma lem3481815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481817 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term343 A f s x) = (term363 A s f x).
Proof. exact (MK_COMB (@lem3481815 A) (@lem3481814 A s f x)). Qed.
Lemma lem3481818 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term363 A s f x.
Proof. exact (EQ_MP (@lem3481817 A s f x) (@lem3481728 A t f s x h1)). Qed.
Lemma lem3481822 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3481844 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term341 A f s t x) = (term361 A s f t x).
Proof. exact (@lem19490 (@I (A -> Prop) s x) (term338 A f t) (@I (A -> Prop) t x)). Qed.
Lemma lem3481845 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term342 A f s x) = (term362 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3481844 A s f t x)). Qed.
Lemma lem3481846 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3481848 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term343 A f s x) = (term363 A s f x).
Proof. exact (MK_COMB (@lem3481846 A) (@lem3481845 A s f x)). Qed.
Lemma lem3481849 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term363 A s f x.
Proof. exact (EQ_MP (@lem3481848 A s f x) (@lem3481728 A t f s x h1)). Qed.
Lemma lem3481861 {A : Type'} (_36704 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term364 A f x _36704.
Proof. exact (@lem3481787 A f s t x h1 _36704). Qed.
Lemma lem3481862 {A : Type'} (f : type686 A) (_36704 : A -> Prop) (x : A) : (term364 A f x _36704) = (term353 A f _36704 x).
Proof. exact (eq_refl (term364 A f x _36704)). Qed.
Lemma lem3481864 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term365 A s f x _36705.
Proof. exact (@lem3481818 A t f s x h1 _36705). Qed.
Lemma lem3481865 {A : Type'} (s : A -> Prop) (f : type686 A) (_36705 : A -> Prop) (x : A) : (term365 A s f x _36705) = (term361 A s f _36705 x).
Proof. exact (eq_refl (term365 A s f x _36705)). Qed.
Lemma lem3481866 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term361 A s f _36705 x.
Proof. exact (EQ_MP (@lem3481865 A s f _36705 x) (@lem3481864 A _36705 t f s x h1)). Qed.
Lemma lem3481867 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term365 A s f x _36706.
Proof. exact (@lem3481849 A t f s x h1 _36706). Qed.
Lemma lem3481868 {A : Type'} (s : A -> Prop) (f : type686 A) (_36706 : A -> Prop) (x : A) : (term365 A s f x _36706) = (term361 A s f _36706 x).
Proof. exact (eq_refl (term365 A s f x _36706)). Qed.
Lemma lem3481869 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term361 A s f _36706 x.
Proof. exact (EQ_MP (@lem3481868 A s f _36706 x) (@lem3481867 A _36706 t f s x h1)). Qed.
Lemma lem3481887 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3481899 {A : Type'} (_36704 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term353 A f _36704 x.
Proof. exact (EQ_MP (@lem3481862 A f _36704 x) (@lem3481861 A _36704 f s t x h1)). Qed.
Lemma lem3481901 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term344 A t x.
Proof. exact (h1). Qed.
Lemma lem3481905 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3481911 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term366 A f _36705 s x.
Proof. exact (proj1 (@lem3481866 A _36705 t f s x h1)). Qed.
Lemma lem3481923 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term344 A t x.
Proof. exact (proj2 (@lem3481731 A f t x h1)). Qed.
Lemma lem3481935 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term353 A f _36706 x.
Proof. exact (proj2 (@lem3481869 A _36706 t f s x h1)). Qed.
Lemma lem3481937 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3481721 A f s t x h1)). Qed.
Lemma lem3481938 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term367 A s x.
Proof. exact (fun h0 : term344 A s x => @lem3481937 A f s t x h1). Qed.
Lemma lem3481940 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3481941 {A : Type'} (s : A -> Prop) (x : A) : (term367 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3481940 (@I (A -> Prop) s x)). Qed.
Lemma lem3481942 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3481941 A s x) (@lem3481938 A f s t x h1)). Qed.
Lemma lem3481945 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3481947 {A : Type'} (s : A -> Prop) (x : A) : (term344 A s x) = (term369 A s x).
Proof. exact (@lem3481945 (@I (A -> Prop) s x)). Qed.
Lemma lem3481950 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term369 A s x.
Proof. exact (EQ_MP (@lem3481947 A s x) (@lem3481887 A s x h1)). Qed.
Lemma lem3481953 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : False.
Proof. exact (@lem3481950 A s x h1 (@lem3481942 A f s t x h2)). Qed.
Lemma lem3481954 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : term370.
Proof. exact (fun h0 : ~ False => @lem3481953 A f s t x h1 h2). Qed.
Lemma lem3481956 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3481957 : term370 = False.
Proof. exact (@lem3481956 False). Qed.
Lemma lem3481958 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3481957) (@lem3481954 A f s t x h1 h2)). Qed.
Lemma lem3481960 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3481720 A f s t x h1)). Qed.
Lemma lem3481961 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term371 A f t.
Proof. exact (fun h0 : term338 A f t => @lem3481960 A f s t x h1). Qed.
Lemma lem3481963 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3481964 {A : Type'} (f : type686 A) (t : A -> Prop) : (term371 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3481963 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3481965 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3481964 A f t) (@lem3481961 A f s t x h1)). Qed.
Lemma lem3481971 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3481972 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : (term353 A f _36704 x) = (term372 A x f _36704).
Proof. exact (@lem3481971 (@I (A -> Prop) _36704 x) (term338 A f _36704)). Qed.
Lemma lem3481978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3481979 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : (term373 A f _36704 x) = (term374 A x f _36704).
Proof. exact (MK_COMB (@lem3481978) (@lem3481972 A x f _36704)). Qed.
Lemma lem3481985 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : (term372 A x f _36704) = (term372 A x f _36704).
Proof. exact (eq_refl (term372 A x f _36704)). Qed.
Lemma lem3481986 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : ((term353 A f _36704 x) = (term372 A x f _36704)) = ((term372 A x f _36704) = (term372 A x f _36704)).
Proof. exact (MK_COMB (@lem3481979 A x f _36704) (@lem3481985 A x f _36704)). Qed.
Lemma lem3481988 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3481989 (x : Prop) : (x = x) = True.
Proof. exact (@lem3481988 Prop x). Qed.
Lemma lem3481990 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : ((term372 A x f _36704) = (term372 A x f _36704)) = True.
Proof. exact (@lem3481989 (term372 A x f _36704)). Qed.
Lemma lem3481991 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : ((term353 A f _36704 x) = (term372 A x f _36704)) = True.
Proof. exact (TRANS (@lem3481986 A x f _36704) (@lem3481990 A x f _36704)). Qed.
Lemma lem3481992 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : True = ((term353 A f _36704 x) = (term372 A x f _36704)).
Proof. exact (SYM (@lem3481991 A x f _36704)). Qed.
Lemma lem3481993 {A : Type'} (x : A) (f : type686 A) (_36704 : A -> Prop) : (term353 A f _36704 x) = (term372 A x f _36704).
Proof. exact (EQ_MP (@lem3481992 A x f _36704) (@lem0)). Qed.
Lemma lem3481994 {A : Type'} (_36704 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term372 A x f _36704.
Proof. exact (EQ_MP (@lem3481993 A x f _36704) (@lem3481899 A _36704 f s t x h1)). Qed.
Lemma lem3481996 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3481997 {A : Type'} (f : type686 A) (_36704 : A -> Prop) (x : A) : (term372 A x f _36704) = (term376 A f _36704 x).
Proof. exact (@lem3481996 (term338 A f _36704) (@I (A -> Prop) _36704 x)). Qed.
Lemma lem3481999 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3482000 {A : Type'} (f : type686 A) (_36704 : A -> Prop) : (term377 A f _36704) = (@I ((A -> Prop) -> Prop) f _36704).
Proof. exact (@lem3481999 (@I ((A -> Prop) -> Prop) f _36704)). Qed.
Lemma lem3482001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482002 {A : Type'} (f : type686 A) (_36704 : A -> Prop) : (term378 A f _36704) = (term379 A f _36704).
Proof. exact (MK_COMB (@lem3482001) (@lem3482000 A f _36704)). Qed.
Lemma lem3482003 {A : Type'} (_36704 : A -> Prop) (x : A) : (@I (A -> Prop) _36704 x) = (@I (A -> Prop) _36704 x).
Proof. exact (eq_refl (@I (A -> Prop) _36704 x)). Qed.
Lemma lem3482004 {A : Type'} (f : type686 A) (_36704 : A -> Prop) (x : A) : (term376 A f _36704 x) = (term380 A f _36704 x).
Proof. exact (MK_COMB (@lem3482002 A f _36704) (@lem3482003 A _36704 x)). Qed.
Lemma lem3482005 {A : Type'} (f : type686 A) (_36704 : A -> Prop) (x : A) : (term372 A x f _36704) = (term380 A f _36704 x).
Proof. exact (TRANS (@lem3481997 A f _36704 x) (@lem3482004 A f _36704 x)). Qed.
Lemma lem3482008 {A : Type'} (_36704 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term380 A f _36704 x.
Proof. exact (EQ_MP (@lem3482005 A f _36704 x) (@lem3481994 A _36704 f s t x h1)). Qed.
Lemma lem3482009 {A : Type'} (_36704 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term380 A f _36704 x.
Proof. exact (@lem3482008 A _36704 f s t x h1). Qed.
Lemma lem3482010 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term380 A f t x.
Proof. exact (@lem3482009 A t f s t x h1). Qed.
Lemma lem3482013 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I (A -> Prop) t x.
Proof. exact (@lem3482010 A f s t x h1 (@lem3481965 A f s t x h1)). Qed.
Lemma lem3482014 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : term367 A t x.
Proof. exact (fun h0 : term344 A t x => @lem3482013 A f s t x h1). Qed.
Lemma lem3482016 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482017 {A : Type'} (t : A -> Prop) (x : A) : (term367 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3482016 (@I (A -> Prop) t x)). Qed.
Lemma lem3482018 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3482017 A t x) (@lem3482014 A f s t x h1)). Qed.
Lemma lem3482021 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3482023 {A : Type'} (t : A -> Prop) (x : A) : (term344 A t x) = (term369 A t x).
Proof. exact (@lem3482021 (@I (A -> Prop) t x)). Qed.
Lemma lem3482026 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term369 A t x.
Proof. exact (EQ_MP (@lem3482023 A t x) (@lem3481901 A t x h1)). Qed.
Lemma lem3482029 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : False.
Proof. exact (@lem3482026 A t x h1 (@lem3482018 A f s t x h2)). Qed.
Lemma lem3482030 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : term370.
Proof. exact (fun h0 : ~ False => @lem3482029 A f s t x h1 h2). Qed.
Lemma lem3482032 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482033 : term370 = False.
Proof. exact (@lem3482032 False). Qed.
Lemma lem3482034 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482033) (@lem3482030 A f s t x h1 h2)). Qed.
Lemma lem3482036 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem3481716 A f x') (@lem3481560 A f x' h1)). Qed.
Lemma lem3482037 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : term371 A f x'.
Proof. exact (fun h0 : term338 A f x' => @lem3482036 A f x' h1). Qed.
Lemma lem3482039 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482040 {A : Type'} (f : type686 A) (x' : A -> Prop) : (term371 A f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3482039 (@I ((A -> Prop) -> Prop) f x')). Qed.
Lemma lem3482041 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem3482040 A f x') (@lem3482037 A f x' h1)). Qed.
Lemma lem3482047 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3482048 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : (term366 A f _36705 s x) = (term381 A s x f _36705).
Proof. exact (@lem3482047 (@I (A -> Prop) s x) (term338 A f _36705)). Qed.
Lemma lem3482054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482055 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : (term382 A f _36705 s x) = (term383 A s x f _36705).
Proof. exact (MK_COMB (@lem3482054) (@lem3482048 A s x f _36705)). Qed.
Lemma lem3482061 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : (term381 A s x f _36705) = (term381 A s x f _36705).
Proof. exact (eq_refl (term381 A s x f _36705)). Qed.
Lemma lem3482062 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : ((term366 A f _36705 s x) = (term381 A s x f _36705)) = ((term381 A s x f _36705) = (term381 A s x f _36705)).
Proof. exact (MK_COMB (@lem3482055 A s x f _36705) (@lem3482061 A s x f _36705)). Qed.
Lemma lem3482064 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3482065 (x : Prop) : (x = x) = True.
Proof. exact (@lem3482064 Prop x). Qed.
Lemma lem3482066 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : ((term381 A s x f _36705) = (term381 A s x f _36705)) = True.
Proof. exact (@lem3482065 (term381 A s x f _36705)). Qed.
Lemma lem3482067 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : ((term366 A f _36705 s x) = (term381 A s x f _36705)) = True.
Proof. exact (TRANS (@lem3482062 A s x f _36705) (@lem3482066 A s x f _36705)). Qed.
Lemma lem3482068 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : True = ((term366 A f _36705 s x) = (term381 A s x f _36705)).
Proof. exact (SYM (@lem3482067 A s x f _36705)). Qed.
Lemma lem3482069 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36705 : A -> Prop) : (term366 A f _36705 s x) = (term381 A s x f _36705).
Proof. exact (EQ_MP (@lem3482068 A s x f _36705) (@lem0)). Qed.
Lemma lem3482070 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term381 A s x f _36705.
Proof. exact (EQ_MP (@lem3482069 A s x f _36705) (@lem3481911 A _36705 t f s x h1)). Qed.
Lemma lem3482072 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3482073 {A : Type'} (f : type686 A) (_36705 : A -> Prop) (s : A -> Prop) (x : A) : (term381 A s x f _36705) = (term384 A f _36705 s x).
Proof. exact (@lem3482072 (term338 A f _36705) (@I (A -> Prop) s x)). Qed.
Lemma lem3482075 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3482076 {A : Type'} (f : type686 A) (_36705 : A -> Prop) : (term377 A f _36705) = (@I ((A -> Prop) -> Prop) f _36705).
Proof. exact (@lem3482075 (@I ((A -> Prop) -> Prop) f _36705)). Qed.
Lemma lem3482077 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482078 {A : Type'} (f : type686 A) (_36705 : A -> Prop) : (term378 A f _36705) = (term379 A f _36705).
Proof. exact (MK_COMB (@lem3482077) (@lem3482076 A f _36705)). Qed.
Lemma lem3482079 {A : Type'} (s : A -> Prop) (x : A) : (@I (A -> Prop) s x) = (@I (A -> Prop) s x).
Proof. exact (eq_refl (@I (A -> Prop) s x)). Qed.
Lemma lem3482080 {A : Type'} (f : type686 A) (_36705 : A -> Prop) (s : A -> Prop) (x : A) : (term384 A f _36705 s x) = (term385 A f _36705 s x).
Proof. exact (MK_COMB (@lem3482078 A f _36705) (@lem3482079 A s x)). Qed.
Lemma lem3482081 {A : Type'} (f : type686 A) (_36705 : A -> Prop) (s : A -> Prop) (x : A) : (term381 A s x f _36705) = (term385 A f _36705 s x).
Proof. exact (TRANS (@lem3482073 A f _36705 s x) (@lem3482080 A f _36705 s x)). Qed.
Lemma lem3482084 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term385 A f _36705 s x.
Proof. exact (EQ_MP (@lem3482081 A f _36705 s x) (@lem3482070 A _36705 t f s x h1)). Qed.
Lemma lem3482085 {A : Type'} (_36705 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term385 A f _36705 s x.
Proof. exact (@lem3482084 A _36705 t f s x h1). Qed.
Lemma lem3482086 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term385 A f x' s x.
Proof. exact (@lem3482085 A x' t f s x h1). Qed.
Lemma lem3482089 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term350 A t f s x) : @I (A -> Prop) s x.
Proof. exact (@lem3482086 A x' t f s x h2 (@lem3482041 A f x' h1)). Qed.
Lemma lem3482090 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term350 A t f s x) : term367 A s x.
Proof. exact (fun h0 : term344 A s x => @lem3482089 A x' t f s x h1 h2). Qed.
Lemma lem3482092 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482093 {A : Type'} (s : A -> Prop) (x : A) : (term367 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3482092 (@I (A -> Prop) s x)). Qed.
Lemma lem3482094 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term350 A t f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3482093 A s x) (@lem3482090 A x' t f s x h1 h2)). Qed.
Lemma lem3482097 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3482099 {A : Type'} (s : A -> Prop) (x : A) : (term344 A s x) = (term369 A s x).
Proof. exact (@lem3482097 (@I (A -> Prop) s x)). Qed.
Lemma lem3482102 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term369 A s x.
Proof. exact (EQ_MP (@lem3482099 A s x) (@lem3481905 A s x h1)). Qed.
Lemma lem3482105 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : False.
Proof. exact (@lem3482102 A s x h1 (@lem3482094 A x' t f s x h2 h3)). Qed.
Lemma lem3482106 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3482105 A x' t f s x h1 h2 h3). Qed.
Lemma lem3482108 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482109 : term370 = False.
Proof. exact (@lem3482108 False). Qed.
Lemma lem3482110 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : False.
Proof. exact (EQ_MP (@lem3482109) (@lem3482106 A x' t f s x h1 h2 h3)). Qed.
Lemma lem3482112 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3481731 A f t x h1)). Qed.
Lemma lem3482113 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term371 A f t.
Proof. exact (fun h0 : term338 A f t => @lem3482112 A f t x h1). Qed.
Lemma lem3482115 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482116 {A : Type'} (f : type686 A) (t : A -> Prop) : (term371 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3482115 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3482117 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3482116 A f t) (@lem3482113 A f t x h1)). Qed.
Lemma lem3482123 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3482124 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : (term353 A f _36706 x) = (term372 A x f _36706).
Proof. exact (@lem3482123 (@I (A -> Prop) _36706 x) (term338 A f _36706)). Qed.
Lemma lem3482130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482131 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : (term373 A f _36706 x) = (term374 A x f _36706).
Proof. exact (MK_COMB (@lem3482130) (@lem3482124 A x f _36706)). Qed.
Lemma lem3482137 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : (term372 A x f _36706) = (term372 A x f _36706).
Proof. exact (eq_refl (term372 A x f _36706)). Qed.
Lemma lem3482138 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : ((term353 A f _36706 x) = (term372 A x f _36706)) = ((term372 A x f _36706) = (term372 A x f _36706)).
Proof. exact (MK_COMB (@lem3482131 A x f _36706) (@lem3482137 A x f _36706)). Qed.
Lemma lem3482140 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3482141 (x : Prop) : (x = x) = True.
Proof. exact (@lem3482140 Prop x). Qed.
Lemma lem3482142 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : ((term372 A x f _36706) = (term372 A x f _36706)) = True.
Proof. exact (@lem3482141 (term372 A x f _36706)). Qed.
Lemma lem3482143 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : ((term353 A f _36706 x) = (term372 A x f _36706)) = True.
Proof. exact (TRANS (@lem3482138 A x f _36706) (@lem3482142 A x f _36706)). Qed.
Lemma lem3482144 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : True = ((term353 A f _36706 x) = (term372 A x f _36706)).
Proof. exact (SYM (@lem3482143 A x f _36706)). Qed.
Lemma lem3482145 {A : Type'} (x : A) (f : type686 A) (_36706 : A -> Prop) : (term353 A f _36706 x) = (term372 A x f _36706).
Proof. exact (EQ_MP (@lem3482144 A x f _36706) (@lem0)). Qed.
Lemma lem3482146 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term372 A x f _36706.
Proof. exact (EQ_MP (@lem3482145 A x f _36706) (@lem3481935 A _36706 t f s x h1)). Qed.
Lemma lem3482148 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3482149 {A : Type'} (f : type686 A) (_36706 : A -> Prop) (x : A) : (term372 A x f _36706) = (term376 A f _36706 x).
Proof. exact (@lem3482148 (term338 A f _36706) (@I (A -> Prop) _36706 x)). Qed.
Lemma lem3482151 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3482152 {A : Type'} (f : type686 A) (_36706 : A -> Prop) : (term377 A f _36706) = (@I ((A -> Prop) -> Prop) f _36706).
Proof. exact (@lem3482151 (@I ((A -> Prop) -> Prop) f _36706)). Qed.
Lemma lem3482153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482154 {A : Type'} (f : type686 A) (_36706 : A -> Prop) : (term378 A f _36706) = (term379 A f _36706).
Proof. exact (MK_COMB (@lem3482153) (@lem3482152 A f _36706)). Qed.
Lemma lem3482155 {A : Type'} (_36706 : A -> Prop) (x : A) : (@I (A -> Prop) _36706 x) = (@I (A -> Prop) _36706 x).
Proof. exact (eq_refl (@I (A -> Prop) _36706 x)). Qed.
Lemma lem3482156 {A : Type'} (f : type686 A) (_36706 : A -> Prop) (x : A) : (term376 A f _36706 x) = (term380 A f _36706 x).
Proof. exact (MK_COMB (@lem3482154 A f _36706) (@lem3482155 A _36706 x)). Qed.
Lemma lem3482157 {A : Type'} (f : type686 A) (_36706 : A -> Prop) (x : A) : (term372 A x f _36706) = (term380 A f _36706 x).
Proof. exact (TRANS (@lem3482149 A f _36706 x) (@lem3482156 A f _36706 x)). Qed.
Lemma lem3482160 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term380 A f _36706 x.
Proof. exact (EQ_MP (@lem3482157 A f _36706 x) (@lem3482146 A _36706 t f s x h1)). Qed.
Lemma lem3482161 {A : Type'} (_36706 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term380 A f _36706 x.
Proof. exact (@lem3482160 A _36706 t f s x h1). Qed.
Lemma lem3482162 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term350 A t f s x) : term380 A f t x.
Proof. exact (@lem3482161 A t t f s x h1). Qed.
Lemma lem3482165 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : @I (A -> Prop) t x.
Proof. exact (@lem3482162 A t f s x h2 (@lem3482117 A f t x h1)). Qed.
Lemma lem3482166 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : term367 A t x.
Proof. exact (fun h0 : term344 A t x => @lem3482165 A t f s x h1 h2). Qed.
Lemma lem3482168 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482169 {A : Type'} (t : A -> Prop) (x : A) : (term367 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3482168 (@I (A -> Prop) t x)). Qed.
Lemma lem3482170 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3482169 A t x) (@lem3482166 A t f s x h1 h2)). Qed.
Lemma lem3482173 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3482175 {A : Type'} (t : A -> Prop) (x : A) : (term344 A t x) = (term369 A t x).
Proof. exact (@lem3482173 (@I (A -> Prop) t x)). Qed.
Lemma lem3482178 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term369 A t x.
Proof. exact (EQ_MP (@lem3482175 A t x) (@lem3481923 A f t x h1)). Qed.
Lemma lem3482181 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : False.
Proof. exact (@lem3482178 A f t x h1 (@lem3482170 A t f s x h1 h2)). Qed.
Lemma lem3482182 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3482181 A t f s x h1 h2). Qed.
Lemma lem3482184 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3482185 : term370 = False.
Proof. exact (@lem3482184 False). Qed.
Lemma lem3482186 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term350 A t f s x) : False.
Proof. exact (EQ_MP (@lem3482185) (@lem3482182 A t f s x h1 h2)). Qed.
Lemma lem3482187 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3482110 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3481905 A s x h1)). Qed.
Lemma lem3482188 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : False.
Proof. exact (EQ_MP (@lem3482187 A x' t f s x h1 h2 h3) (@lem3481905 A s x h1)). Qed.
Lemma lem3482189 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3482034 A f s t x h1 h2) (fun h3 : False => @lem3481901 A t x h1)). Qed.
Lemma lem3482190 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482189 A f s t x h1 h2) (@lem3481901 A t x h1)). Qed.
Lemma lem3482191 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3481958 A f s t x h1 h2) (fun h3 : False => @lem3481887 A s x h1)). Qed.
Lemma lem3482192 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482191 A f s t x h1 h2) (@lem3481887 A s x h1)). Qed.
Lemma lem3482193 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3482188 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3481822 A s x h1)). Qed.
Lemma lem3482194 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : False.
Proof. exact (EQ_MP (@lem3482193 A x' t f s x h1 h2 h3) (@lem3481822 A s x h1)). Qed.
Lemma lem3482195 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3482190 A f s t x h1 h2) (fun h3 : False => @lem3481791 A t x h1)). Qed.
Lemma lem3482196 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482195 A f s t x h1 h2) (@lem3481791 A t x h1)). Qed.
Lemma lem3482197 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3482192 A f s t x h1 h2) (fun h3 : False => @lem3481762 A s x h1)). Qed.
Lemma lem3482198 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482197 A f s t x h1 h2) (@lem3481762 A s x h1)). Qed.
Lemma lem3482199 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3482194 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3481822 A s x h1)). Qed.
Lemma lem3482200 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term350 A t f s x) : False.
Proof. exact (EQ_MP (@lem3482199 A x' t f s x h1 h2 h3) (@lem3481822 A s x h1)). Qed.
Lemma lem3482201 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3482196 A f s t x h1 h2) (fun h3 : False => @lem3481791 A t x h1)). Qed.
Lemma lem3482202 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482201 A f s t x h1 h2) (@lem3481791 A t x h1)). Qed.
Lemma lem3482203 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3482198 A f s t x h1 h2) (fun h3 : False => @lem3481762 A s x h1)). Qed.
Lemma lem3482204 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term358 A f s t x) : False.
Proof. exact (EQ_MP (@lem3482203 A f s t x h1 h2) (@lem3481762 A s x h1)). Qed.
Lemma lem3482205 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term350 A t f s x) : False.
Proof. exact (or_elim (@lem3481729 A t f s x h2) (fun h0 : term344 A s x => @lem3482200 A x' t f s x h0 h1 h2) (fun h0 : term346 A f t x => @lem3482186 A t f s x h0 h2)). Qed.
Lemma lem3482206 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term358 A f s t x) : False.
Proof. exact (or_elim (@lem3481722 A f s t x h1) (fun h0 : term344 A s x => @lem3482204 A f s t x h0 h1) (fun h0 : term344 A t x => @lem3482202 A f s t x h0 h1)). Qed.
Lemma lem3482207 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term332 A t f s x) : False.
Proof. exact (or_elim (@lem3481708 A t f s x h2) (fun h0 : term358 A f s t x => @lem3482206 A f s t x h0) (fun h0 : term350 A t f s x => @lem3482205 A x' t f s x h1 h0)). Qed.
Lemma lem3482208 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term332 A t f s x) : False.
Proof. exact (ex_elim (@lem3481217 A f h1) (fun x' : A -> Prop => fun h0 : term211 A f x' => @lem3482207 A x' t f s x h0 h2)). Qed.
Lemma lem3482209 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term203 A f s x) : False.
Proof. exact (ex_elim (@lem3481558 A f s x h2) (fun t : A -> Prop => fun h0 : term334 A f s x t => @lem3482208 A t f s x h1 h0)). Qed.
Lemma lem3482210 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term203 A f s x) : (term203 A f s x) = False.
Proof. exact (prop_ext (fun h3 : term203 A f s x => @lem3482209 A f s x h1 h2) (fun h3 : False => @lem3481195 A f s x h2)). Qed.
Lemma lem3482211 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term203 A f s x) : False.
Proof. exact (EQ_MP (@lem3482210 A f s x h1 h2) (@lem3481195 A f s x h2)). Qed.
Lemma lem3482212 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term147 A f) : term202 A f s x.
Proof. exact (fun h0 : term203 A f s x => @lem3482211 A f s x h1 h0). Qed.
Lemma lem3482213 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term147 A f) : (term162 A s f x) = (term181 A f s x).
Proof. exact (EQ_MP (@lem3481194 A f s x) (@lem3482212 A s x f h1)). Qed.
Lemma lem3482218 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term147 A f) : term184 A f s.
Proof. exact (fun x : A => @lem3482213 A s x f h1). Qed.
Lemma lem3482219 {A : Type'} (f : type686 A) (s : A -> Prop) : term185 A f s.
Proof. exact (fun h0 : term147 A f => @lem3482218 A s f h0). Qed.
Lemma lem3482224 {A : Type'} (s : A -> Prop) : term197 A s.
Proof. exact (fun f : type686 A => @lem3482219 A f s). Qed.
Lemma lem3482229 {A : Type'} : term201 A.
Proof. exact (fun s : A -> Prop => @lem3482224 A s). Qed.
Lemma lem3482230 {A : Type'} : term200 A.
Proof. exact (EQ_MP (@lem3481189 A) (@lem3482229 A)). Qed.
Lemma lem3482231 {A : Type'} (s : A -> Prop) : term386 A s.
Proof. exact (@lem3482230 A s). Qed.
Lemma lem3482232 {A : Type'} (s : A -> Prop) : (term386 A s) = (term196 A s).
Proof. exact (eq_refl (term386 A s)). Qed.
Lemma lem3482233 {A : Type'} (s : A -> Prop) : term196 A s.
Proof. exact (EQ_MP (@lem3482232 A s) (@lem3482231 A s)). Qed.
Lemma lem3482234 {A : Type'} (s : A -> Prop) (f : type686 A) : term387 A s f.
Proof. exact (@lem3482233 A s f). Qed.
Lemma lem3482235 {A : Type'} (f : type686 A) (s : A -> Prop) : (term387 A s f) = (term187 A f s).
Proof. exact (eq_refl (term387 A s f)). Qed.
Lemma lem3482236 {A : Type'} (f : type686 A) (s : A -> Prop) : term187 A f s.
Proof. exact (EQ_MP (@lem3482235 A f s) (@lem3482234 A s f)). Qed.
Lemma lem3482238 {A : Type'} (f : type686 A) (s : A -> Prop) : term187 A f s.
Proof. exact (@lem3481033 A f s (@lem3482236 A f s)). Qed.
Lemma lem3482239 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term188 A f s) : False.
Proof. exact (@lem3482238 A f s (@lem3481017 A f s h1)). Qed.
Lemma lem3482240 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term188 A f s) : (term188 A f s) = False.
Proof. exact (prop_ext (fun h2 : term188 A f s => @lem3482239 A f s h1) (fun h2 : False => @lem3481017 A f s h1)). Qed.
Lemma lem3482241 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term188 A f s) : False.
Proof. exact (EQ_MP (@lem3482240 A f s h1) (@lem3481017 A f s h1)). Qed.
Lemma lem3482242 {A : Type'} (f : type686 A) (s : A -> Prop) : term187 A f s.
Proof. exact (fun h0 : term188 A f s => @lem3482241 A f s h0). Qed.
Lemma lem3482243 {A : Type'} (f : type686 A) (s : A -> Prop) : term185 A f s.
Proof. exact (EQ_MP (@lem3481016 A f s) (@lem3482242 A f s)). Qed.
Lemma lem3482244 {A : Type'} (f : type686 A) (s : A -> Prop) : term140 A f s.
Proof. exact (EQ_MP (@lem3481012 A f s) (@lem3482243 A f s)). Qed.
Lemma lem3482245 {A : Type'} (f : type686 A) (s : A -> Prop) : term139 A f s.
Proof. exact (EQ_MP (@lem3480846 A f s) (@lem3482244 A f s)). Qed.
Lemma lem3482246 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term9 A s f) = (term94 A f s).
Proof. exact (@lem3482245 A f s (@lem3480404 A f h1)). Qed.
Lemma lem3482262 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3482263 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term134 A s t).
Proof. exact (@lem3482262 (A -> Prop) s t). Qed.
Lemma lem3482264 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term135 A f).
Proof. exact (@lem3482263 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3482273 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482274 {A : Type'} (f : type686 A) : (term23 A f) = (term136 A f).
Proof. exact (MK_COMB (@lem3482273) (@lem3482264 A f)). Qed.
Lemma lem3482275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482276 {A : Type'} (f : type686 A) : (term10 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3482275) (@lem3482274 A f)). Qed.
Lemma lem3482280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3482281 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (@lem3482280 A s t). Qed.
Lemma lem3482282 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term31 A f s) = (term132 A f s)) = (term388 A f s).
Proof. exact (@lem3482281 A (term31 A f s) (term132 A f s)). Qed.
Lemma lem3482301 {A : Type'} (f : type686 A) (s : A -> Prop) : (term389 A f s) = (term390 A f s).
Proof. exact (MK_COMB (@lem3482276 A f) (@lem3482282 A f s)). Qed.
Lemma lem3482304 {A : Type'} (f : type686 A) (s : A -> Prop) : (term390 A f s) = (term389 A f s).
Proof. exact (SYM (@lem3482301 A f s)). Qed.
Lemma lem3482314 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482315 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3482314 (A -> Prop) P x). Qed.
Lemma lem3482316 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3482315 A f x). Qed.
Lemma lem3482317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482318 {A : Type'} (f : type686 A) (x : A -> Prop) : (term141 A x f) = (term142 A f x).
Proof. exact (MK_COMB (@lem3482317) (@lem3482316 A f x)). Qed.
Lemma lem3482320 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3482321 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3482320 (A -> Prop) x). Qed.
Lemma lem3482322 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3482318 A f x) (@lem3482321 A x)). Qed.
Lemma lem3482324 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3482325 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term143 A f x).
Proof. exact (@lem3482324 (f x)). Qed.
Lemma lem3482326 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term143 A f x).
Proof. exact (TRANS (@lem3482322 A f x) (@lem3482325 A f x)). Qed.
Lemma lem3482327 {A : Type'} (f : type686 A) : (term144 A f) = (term145 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3482326 A f x)). Qed.
Lemma lem3482328 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482329 {A : Type'} (f : type686 A) : (term135 A f) = (term146 A f).
Proof. exact (MK_COMB (@lem3482328 A) (@lem3482327 A f)). Qed.
Lemma lem3482334 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482335 {A : Type'} (f : type686 A) : (term136 A f) = (term147 A f).
Proof. exact (MK_COMB (@lem3482334) (@lem3482329 A f)). Qed.
Lemma lem3482336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482337 {A : Type'} (f : type686 A) : (term137 A f) = (term148 A f).
Proof. exact (MK_COMB (@lem3482336) (@lem3482335 A f)). Qed.
Lemma lem3482345 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3482346 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (@lem3482345 A s x t). Qed.
Lemma lem3482347 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : (term391 A x f s) = (term392 A f x s).
Proof. exact (@lem3482346 A (@INTERS A f) x s). Qed.
Lemma lem3482351 {A : Type'} (s : type686 A) (x : A) : (term154 A x s) = (term155 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3482352 {A : Type'} (s : type686 A) (x : A) : (term154 A x s) = (term155 A s x).
Proof. exact (@lem3482351 A s x). Qed.
Lemma lem3482353 {A : Type'} (f : type686 A) (x : A) : (term154 A x f) = (term155 A f x).
Proof. exact (@lem3482352 A f x). Qed.
Lemma lem3482361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482362 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3482361 (A -> Prop) P x). Qed.
Lemma lem3482363 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3482362 A f t). Qed.
Lemma lem3482364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482365 {A : Type'} (f : type686 A) (t : A -> Prop) : (term75 A t f) = (term156 A f t).
Proof. exact (MK_COMB (@lem3482364) (@lem3482363 A f t)). Qed.
Lemma lem3482367 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482368 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3482367 A P x). Qed.
Lemma lem3482369 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3482368 A t x). Qed.
Lemma lem3482370 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term157 A f x t) = (term158 A f t x).
Proof. exact (MK_COMB (@lem3482365 A f t) (@lem3482369 A t x)). Qed.
Lemma lem3482373 {A : Type'} (f : type686 A) (x : A) : (term159 A f x) = (term160 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482370 A f t x)). Qed.
Lemma lem3482374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482375 {A : Type'} (f : type686 A) (x : A) : (term155 A f x) = (term161 A f x).
Proof. exact (MK_COMB (@lem3482374 A) (@lem3482373 A f x)). Qed.
Lemma lem3482380 {A : Type'} (f : type686 A) (x : A) : (term154 A x f) = (term161 A f x).
Proof. exact (TRANS (@lem3482353 A f x) (@lem3482375 A f x)). Qed.
Lemma lem3482381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482382 {A : Type'} (f : type686 A) (x : A) : (term393 A x f) = (term394 A f x).
Proof. exact (MK_COMB (@lem3482381) (@lem3482380 A f x)). Qed.
Lemma lem3482384 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3482384 A P x). Qed.
Lemma lem3482386 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3482385 A s x). Qed.
Lemma lem3482387 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term392 A f x s) = (term395 A f s x).
Proof. exact (MK_COMB (@lem3482382 A f x) (@lem3482386 A s x)). Qed.
Lemma lem3482390 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term391 A x f s) = (term395 A f s x).
Proof. exact (TRANS (@lem3482347 A f x s) (@lem3482387 A f s x)). Qed.
Lemma lem3482391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482392 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term396 A x f s) = (term397 A f s x).
Proof. exact (MK_COMB (@lem3482391) (@lem3482390 A f s x)). Qed.
Lemma lem3482394 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term165 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3482395 {A : Type'} (p : A -> Prop) (x : A) : (term165 A x p) = (p x).
Proof. exact (@lem3482394 A p x). Qed.
Lemma lem3482396 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term398 A x f s) = (term399 A f s x).
Proof. exact (@lem3482395 A (term400 A f s) x). Qed.
Lemma lem3482397 {A : Type'} (f : type686 A) (a : A) (s : A -> Prop) : (term399 A f s a) = (term121 A f a s).
Proof. exact (eq_refl (term399 A f s a)). Qed.
Lemma lem3482398 {A : Type'} (GEN_PVAR_56 : A) : (@SETSPEC A GEN_PVAR_56) = (@SETSPEC A GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_56)). Qed.
Lemma lem3482399 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (a : A) (s : A -> Prop) : (term401 A GEN_PVAR_56 f s a) = (term123 A GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3482398 A GEN_PVAR_56) (@lem3482397 A f a s)). Qed.
Lemma lem3482400 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3482401 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) (a : A) : (term402 A GEN_PVAR_56 f s a) = (term125 A GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3482399 A GEN_PVAR_56 f a s) (@lem3482400 A a)). Qed.
Lemma lem3482402 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term403 A GEN_PVAR_56 f s) = (term127 A GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : A => @lem3482401 A GEN_PVAR_56 f s a)). Qed.
Lemma lem3482403 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3482404 {A : Type'} (GEN_PVAR_56 : A) (f : type686 A) (s : A -> Prop) : (term404 A GEN_PVAR_56 f s) = (term129 A GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3482403 A) (@lem3482402 A GEN_PVAR_56 f s)). Qed.
Lemma lem3482405 {A : Type'} (f : type686 A) (s : A -> Prop) : (term405 A f s) = (term131 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : A => @lem3482404 A GEN_PVAR_56 f s)). Qed.
Lemma lem3482406 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3482407 {A : Type'} (f : type686 A) (s : A -> Prop) : (term406 A f s) = (term132 A f s).
Proof. exact (MK_COMB (@lem3482406 A) (@lem3482405 A f s)). Qed.
Lemma lem3482408 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3482409 {A : Type'} (x : A) (f : type686 A) (s : A -> Prop) : (term398 A x f s) = (term407 A x f s).
Proof. exact (MK_COMB (@lem3482408 A x) (@lem3482407 A f s)). Qed.
Lemma lem3482410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482411 {A : Type'} (x : A) (f : type686 A) (s : A -> Prop) : (term408 A x f s) = (term409 A x f s).
Proof. exact (MK_COMB (@lem3482410) (@lem3482409 A x f s)). Qed.
Lemma lem3482412 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : (term399 A f s x) = (term121 A f x s).
Proof. exact (eq_refl (term399 A f s x)). Qed.
Lemma lem3482413 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : ((term398 A x f s) = (term399 A f s x)) = ((term407 A x f s) = (term121 A f x s)).
Proof. exact (MK_COMB (@lem3482411 A x f s) (@lem3482412 A f x s)). Qed.
Lemma lem3482414 {A : Type'} (f : type686 A) (x : A) (s : A -> Prop) : (term407 A x f s) = (term121 A f x s).
Proof. exact (EQ_MP (@lem3482413 A f x s) (@lem3482396 A f s x)). Qed.
Lemma lem3482422 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482423 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3482422 (A -> Prop) P x). Qed.
Lemma lem3482424 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3482423 A f t). Qed.
Lemma lem3482425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482426 {A : Type'} (f : type686 A) (t : A -> Prop) : (term75 A t f) = (term156 A f t).
Proof. exact (MK_COMB (@lem3482425) (@lem3482424 A f t)). Qed.
Lemma lem3482428 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3482429 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term77 A x s t) = (term149 A s x t).
Proof. exact (@lem3482428 A s x t). Qed.
Lemma lem3482430 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term77 A x t s) = (term149 A t x s).
Proof. exact (@lem3482429 A t x s). Qed.
Lemma lem3482434 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482435 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3482434 A P x). Qed.
Lemma lem3482436 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3482435 A t x). Qed.
Lemma lem3482437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482438 {A : Type'} (t : A -> Prop) (x : A) : (term152 A x t) = (term153 A t x).
Proof. exact (MK_COMB (@lem3482437) (@lem3482436 A t x)). Qed.
Lemma lem3482440 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3482441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3482440 A P x). Qed.
Lemma lem3482442 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3482441 A s x). Qed.
Lemma lem3482443 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term149 A t x s) = (term178 A t s x).
Proof. exact (MK_COMB (@lem3482438 A t x) (@lem3482442 A s x)). Qed.
Lemma lem3482446 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term77 A x t s) = (term178 A t s x).
Proof. exact (TRANS (@lem3482430 A t x s) (@lem3482443 A t s x)). Qed.
Lemma lem3482447 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term117 A f x t s) = (term410 A f t s x).
Proof. exact (MK_COMB (@lem3482426 A f t) (@lem3482446 A t s x)). Qed.
Lemma lem3482450 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term119 A f x s) = (term411 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482447 A f t s x)). Qed.
Lemma lem3482451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482452 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term121 A f x s) = (term412 A f s x).
Proof. exact (MK_COMB (@lem3482451 A) (@lem3482450 A f s x)). Qed.
Lemma lem3482457 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term407 A x f s) = (term412 A f s x).
Proof. exact (TRANS (@lem3482414 A f x s) (@lem3482452 A f s x)). Qed.
Lemma lem3482458 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term391 A x f s) = (term407 A x f s)) = ((term395 A f s x) = (term412 A f s x)).
Proof. exact (MK_COMB (@lem3482392 A f s x) (@lem3482457 A f s x)). Qed.
Lemma lem3482461 {A : Type'} (f : type686 A) (s : A -> Prop) : (term413 A f s) = (term414 A f s).
Proof. exact (fun_ext (fun x : A => @lem3482458 A f s x)). Qed.
Lemma lem3482462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3482463 {A : Type'} (f : type686 A) (s : A -> Prop) : (term388 A f s) = (term415 A f s).
Proof. exact (MK_COMB (@lem3482462 A) (@lem3482461 A f s)). Qed.
Lemma lem3482468 {A : Type'} (f : type686 A) (s : A -> Prop) : (term390 A f s) = (term416 A f s).
Proof. exact (MK_COMB (@lem3482337 A f) (@lem3482463 A f s)). Qed.
Lemma lem3482471 {A : Type'} (f : type686 A) (s : A -> Prop) : (term416 A f s) = (term390 A f s).
Proof. exact (SYM (@lem3482468 A f s)). Qed.
Lemma lem3482473 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3482474 {A : Type'} (f : type686 A) (s : A -> Prop) : (term416 A f s) = (term417 A f s).
Proof. exact (@lem3482473 (term416 A f s)). Qed.
Lemma lem3482475 {A : Type'} (f : type686 A) (s : A -> Prop) : (term417 A f s) = (term416 A f s).
Proof. exact (SYM (@lem3482474 A f s)). Qed.
Lemma lem3482476 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term418 A f s) : term418 A f s.
Proof. exact (h1). Qed.
Lemma lem3482479 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term417 A f s) : term417 A f s.
Proof. exact (h1). Qed.
Lemma lem3482480 {A : Type'} (f : type686 A) (s : A -> Prop) : term419 A f s.
Proof. exact (fun h0 : term417 A f s => @lem3482479 A f s h0). Qed.
Lemma lem3482481 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term419 A f s) : term419 A f s.
Proof. exact (h1). Qed.
Lemma lem3482482 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term417 A f s) : term417 A f s.
Proof. exact (h1). Qed.
Lemma lem3482483 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term417 A f s) (h2 : term419 A f s) : term417 A f s.
Proof. exact (@lem3482481 A f s h2 (@lem3482482 A f s h1)). Qed.
Lemma lem3482484 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term417 A f s) : term420 A f s.
Proof. exact (fun h0 : term419 A f s => @lem3482483 A f s h1 h0). Qed.
Lemma lem3482485 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term419 A f s) : term419 A f s.
Proof. exact (h1). Qed.
Lemma lem3482486 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term417 A f s) (h2 : term419 A f s) : term417 A f s.
Proof. exact (@lem3482484 A f s h1 (@lem3482485 A f s h2)). Qed.
Lemma lem3482487 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term419 A f s) : term419 A f s.
Proof. exact (fun h0 : term417 A f s => @lem3482486 A f s h0 h1). Qed.
Lemma lem3482488 {A : Type'} (f : type686 A) (s : A -> Prop) : term421 A f s.
Proof. exact (fun h0 : term419 A f s => @lem3482487 A f s h0). Qed.
Lemma lem3482491 {A : Type'} (f : type686 A) (s : A -> Prop) : term419 A f s.
Proof. exact (@lem3482488 A f s (@lem3482480 A f s)). Qed.
Lemma lem3482492 {A : Type'} (f : type686 A) (s : A -> Prop) : term419 A f s.
Proof. exact (@lem3482491 A f s). Qed.
Lemma lem3482502 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3482503 {A : Type'} (f : type686 A) (s : A -> Prop) : (term417 A f s) = (term422 A f s).
Proof. exact (@lem3482502 (term418 A f s)). Qed.
Lemma lem3482505 (t : Prop) : (term193 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3482506 {A : Type'} (f : type686 A) (s : A -> Prop) : (term422 A f s) = (term416 A f s).
Proof. exact (@lem3482505 (term416 A f s)). Qed.
Lemma lem3482509 {A : Type'} (f : type686 A) (s : A -> Prop) : (term417 A f s) = (term416 A f s).
Proof. exact (TRANS (@lem3482503 A f s) (@lem3482506 A f s)). Qed.
Lemma lem3482534 {A : Type'} (s : A -> Prop) : (term423 A s) = (term424 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3482509 A f s)). Qed.
Lemma lem3482535 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3482536 {A : Type'} (s : A -> Prop) : (term425 A s) = (term426 A s).
Proof. exact (MK_COMB (@lem3482535 A) (@lem3482534 A s)). Qed.
Lemma lem3482541 {A : Type'} : (term427 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3482536 A s)). Qed.
Lemma lem3482542 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482551 {A : Type'} : (term429 A) = (term430 A).
Proof. exact (MK_COMB (@lem3482542 A) (@lem3482541 A)). Qed.
Lemma lem3482560 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term410 A f t s x) = (term410 A f t s x).
Proof. exact (eq_refl (term410 A f t s x)). Qed.
Lemma lem3482561 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term411 A f s x) = (term411 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482560 A f t s x)). Qed.
Lemma lem3482562 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482563 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term412 A f s x) = (term412 A f s x).
Proof. exact (MK_COMB (@lem3482562 A) (@lem3482561 A f s x)). Qed.
Lemma lem3482564 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3482569 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term158 A f t x) = (term158 A f t x).
Proof. exact (eq_refl (term158 A f t x)). Qed.
Lemma lem3482570 {A : Type'} (f : type686 A) (x : A) : (term160 A f x) = (term160 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482569 A f t x)). Qed.
Lemma lem3482571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482572 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term161 A f x).
Proof. exact (MK_COMB (@lem3482571 A) (@lem3482570 A f x)). Qed.
Lemma lem3482573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482574 {A : Type'} (f : type686 A) (x : A) : (term394 A f x) = (term394 A f x).
Proof. exact (MK_COMB (@lem3482573) (@lem3482572 A f x)). Qed.
Lemma lem3482575 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term395 A f s x) = (term395 A f s x).
Proof. exact (MK_COMB (@lem3482574 A f x) (@lem3482564 A s x)). Qed.
Lemma lem3482576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482577 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term397 A f s x) = (term397 A f s x).
Proof. exact (MK_COMB (@lem3482576) (@lem3482575 A f s x)). Qed.
Lemma lem3482578 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term395 A f s x) = (term412 A f s x)) = ((term395 A f s x) = (term412 A f s x)).
Proof. exact (MK_COMB (@lem3482577 A f s x) (@lem3482563 A f s x)). Qed.
Lemma lem3482579 {A : Type'} (f : type686 A) (s : A -> Prop) : (term414 A f s) = (term414 A f s).
Proof. exact (fun_ext (fun x : A => @lem3482578 A f s x)). Qed.
Lemma lem3482580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3482581 {A : Type'} (f : type686 A) (s : A -> Prop) : (term415 A f s) = (term415 A f s).
Proof. exact (MK_COMB (@lem3482580 A) (@lem3482579 A f s)). Qed.
Lemma lem3482584 {A : Type'} (f : type686 A) (x : A -> Prop) : (term143 A f x) = (term143 A f x).
Proof. exact (eq_refl (term143 A f x)). Qed.
Lemma lem3482585 {A : Type'} (f : type686 A) : (term145 A f) = (term145 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3482584 A f x)). Qed.
Lemma lem3482586 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482587 {A : Type'} (f : type686 A) : (term146 A f) = (term146 A f).
Proof. exact (MK_COMB (@lem3482586 A) (@lem3482585 A f)). Qed.
Lemma lem3482588 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482589 {A : Type'} (f : type686 A) : (term147 A f) = (term147 A f).
Proof. exact (MK_COMB (@lem3482588) (@lem3482587 A f)). Qed.
Lemma lem3482590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3482591 {A : Type'} (f : type686 A) : (term148 A f) = (term148 A f).
Proof. exact (MK_COMB (@lem3482590) (@lem3482589 A f)). Qed.
Lemma lem3482592 {A : Type'} (f : type686 A) (s : A -> Prop) : (term416 A f s) = (term416 A f s).
Proof. exact (MK_COMB (@lem3482591 A f) (@lem3482581 A f s)). Qed.
Lemma lem3482593 {A : Type'} (s : A -> Prop) : (term424 A s) = (term424 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3482592 A f s)). Qed.
Lemma lem3482594 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3482595 {A : Type'} (s : A -> Prop) : (term426 A s) = (term426 A s).
Proof. exact (MK_COMB (@lem3482594 A) (@lem3482593 A s)). Qed.
Lemma lem3482596 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3482595 A s)). Qed.
Lemma lem3482597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482598 {A : Type'} : (term430 A) = (term430 A).
Proof. exact (MK_COMB (@lem3482597 A) (@lem3482596 A)). Qed.
Lemma lem3482647 {A : Type'} : (term429 A) = (term430 A).
Proof. exact (TRANS (@lem3482551 A) (@lem3482598 A)). Qed.
Lemma lem3482648 {A : Type'} : (term430 A) = (term429 A).
Proof. exact (SYM (@lem3482647 A)). Qed.
Lemma lem3482649 {A : Type'} (f : type686 A) (h1 : term147 A f) : term147 A f.
Proof. exact (h1). Qed.
Lemma lem3482651 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3482652 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term395 A f s x) = (term412 A f s x)) = (term431 A f s x).
Proof. exact (@lem3482651 ((term395 A f s x) = (term412 A f s x))). Qed.
Lemma lem3482653 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term431 A f s x) = ((term395 A f s x) = (term412 A f s x)).
Proof. exact (SYM (@lem3482652 A f s x)). Qed.
Lemma lem3482654 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term432 A f s x) : term432 A f s x.
Proof. exact (h1). Qed.
Lemma lem3482657 {A : Type'} (f : type686 A) (x : A -> Prop) : (term204 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3482658 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3482659 {A : Type'} (f : type686 A) : (term147 A f) = (term207 A f).
Proof. exact (@lem3482658 A (term145 A f)). Qed.
Lemma lem3482660 {A : Type'} (f : type686 A) (x : A -> Prop) : (term208 A f x) = (term143 A f x).
Proof. exact (eq_refl (term208 A f x)). Qed.
Lemma lem3482661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482662 {A : Type'} (f : type686 A) (x : A -> Prop) : (term209 A f x) = (term204 A f x).
Proof. exact (MK_COMB (@lem3482661) (@lem3482660 A f x)). Qed.
Lemma lem3482663 {A : Type'} (f : type686 A) (x : A -> Prop) : (term209 A f x) = (f x).
Proof. exact (TRANS (@lem3482662 A f x) (@lem3482657 A f x)). Qed.
Lemma lem3482664 {A : Type'} (f : type686 A) : (term210 A f) = (term211 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3482663 A f x)). Qed.
Lemma lem3482665 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482666 {A : Type'} (f : type686 A) : (term207 A f) = (term212 A f).
Proof. exact (MK_COMB (@lem3482665 A) (@lem3482664 A f)). Qed.
Lemma lem3482675 {A : Type'} (f : type686 A) : (term147 A f) = (term212 A f).
Proof. exact (TRANS (@lem3482659 A f) (@lem3482666 A f)). Qed.
Lemma lem3482676 {A : Type'} (f : type686 A) (h1 : term147 A f) : term212 A f.
Proof. exact (EQ_MP (@lem3482675 A f) (@lem3482649 A f h1)). Qed.
Lemma lem3482685 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term213 A f t x) = (term214 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3482690 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term158 A f t x) = (term215 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3482691 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3482692 {A : Type'} (f : type686 A) (x : A) : (term216 A f x) = (term217 A f x).
Proof. exact (@lem3482691 A (term160 A f x)). Qed.
Lemma lem3482693 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term218 A f x t) = (term158 A f t x).
Proof. exact (eq_refl (term218 A f x t)). Qed.
Lemma lem3482694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482695 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term219 A f x t) = (term213 A f t x).
Proof. exact (MK_COMB (@lem3482694) (@lem3482693 A f t x)). Qed.
Lemma lem3482696 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term219 A f x t) = (term214 A f t x).
Proof. exact (TRANS (@lem3482695 A f t x) (@lem3482685 A f t x)). Qed.
Lemma lem3482697 {A : Type'} (f : type686 A) (x : A) : (term220 A f x) = (term221 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482696 A f t x)). Qed.
Lemma lem3482698 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482699 {A : Type'} (f : type686 A) (x : A) : (term217 A f x) = (term222 A f x).
Proof. exact (MK_COMB (@lem3482698 A) (@lem3482697 A f x)). Qed.
Lemma lem3482700 {A : Type'} (f : type686 A) (x : A) : (term216 A f x) = (term222 A f x).
Proof. exact (TRANS (@lem3482692 A f x) (@lem3482699 A f x)). Qed.
Lemma lem3482701 {A : Type'} (f : type686 A) (x : A) : (term160 A f x) = (term223 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482690 A f t x)). Qed.
Lemma lem3482702 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482703 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term224 A f x).
Proof. exact (MK_COMB (@lem3482702 A) (@lem3482701 A f x)). Qed.
Lemma lem3482704 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term281 A s x).
Proof. exact (eq_refl (term281 A s x)). Qed.
Lemma lem3482705 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3482706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3482707 {A : Type'} (f : type686 A) (x : A) : (term433 A f x) = (term434 A f x).
Proof. exact (MK_COMB (@lem3482706) (@lem3482700 A f x)). Qed.
Lemma lem3482708 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term435 A f s x) = (term436 A f s x).
Proof. exact (MK_COMB (@lem3482707 A f x) (@lem3482704 A s x)). Qed.
Lemma lem3482709 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term437 A f s x) = (term435 A f s x).
Proof. exact (@lem17045 (term161 A f x) (s x)). Qed.
Lemma lem3482710 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term437 A f s x) = (term436 A f s x).
Proof. exact (TRANS (@lem3482709 A f s x) (@lem3482708 A f s x)). Qed.
Lemma lem3482711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482712 {A : Type'} (f : type686 A) (x : A) : (term394 A f x) = (term438 A f x).
Proof. exact (MK_COMB (@lem3482711) (@lem3482703 A f x)). Qed.
Lemma lem3482713 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term395 A f s x) = (term439 A f s x).
Proof. exact (MK_COMB (@lem3482712 A f x) (@lem3482705 A s x)). Qed.
Lemma lem3482724 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term230 A t s x) = (term231 A t s x).
Proof. exact (@lem17045 (t x) (s x)). Qed.
Lemma lem3482729 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term232 A f t).
Proof. exact (eq_refl (term232 A f t)). Qed.
Lemma lem3482730 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term440 A f t s x) = (term441 A f t s x).
Proof. exact (MK_COMB (@lem3482729 A f t) (@lem3482724 A t s x)). Qed.
Lemma lem3482731 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term442 A f t s x) = (term440 A f t s x).
Proof. exact (@lem17362 (f t) (term178 A t s x)). Qed.
Lemma lem3482732 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term442 A f t s x) = (term441 A f t s x).
Proof. exact (TRANS (@lem3482731 A f t s x) (@lem3482730 A f t s x)). Qed.
Lemma lem3482737 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term410 A f t s x) = (term443 A f t s x).
Proof. exact (@lem17265 (f t) (term178 A t s x)). Qed.
Lemma lem3482738 {A : Type'} (P : type686 A) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3482739 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term444 A f s x) = (term445 A f s x).
Proof. exact (@lem3482738 A (term411 A f s x)). Qed.
Lemma lem3482740 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term446 A f s x t) = (term410 A f t s x).
Proof. exact (eq_refl (term446 A f s x t)). Qed.
Lemma lem3482741 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3482742 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term447 A f s x t) = (term442 A f t s x).
Proof. exact (MK_COMB (@lem3482741) (@lem3482740 A f t s x)). Qed.
Lemma lem3482743 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term447 A f s x t) = (term441 A f t s x).
Proof. exact (TRANS (@lem3482742 A f t s x) (@lem3482732 A f t s x)). Qed.
Lemma lem3482744 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term448 A f s x) = (term449 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482743 A f t s x)). Qed.
Lemma lem3482745 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482746 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term445 A f s x) = (term450 A f s x).
Proof. exact (MK_COMB (@lem3482745 A) (@lem3482744 A f s x)). Qed.
Lemma lem3482747 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term444 A f s x) = (term450 A f s x).
Proof. exact (TRANS (@lem3482739 A f s x) (@lem3482746 A f s x)). Qed.
Lemma lem3482748 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term411 A f s x) = (term451 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482737 A f t s x)). Qed.
Lemma lem3482749 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3482750 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term412 A f s x) = (term452 A f s x).
Proof. exact (MK_COMB (@lem3482749 A) (@lem3482748 A f s x)). Qed.
Lemma lem3482751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482752 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term453 A f s x) = (term454 A f s x).
Proof. exact (MK_COMB (@lem3482751) (@lem3482710 A f s x)). Qed.
Lemma lem3482753 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term455 A f s x) = (term456 A f s x).
Proof. exact (MK_COMB (@lem3482752 A f s x) (@lem3482750 A f s x)). Qed.
Lemma lem3482754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482755 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term457 A f s x) = (term458 A f s x).
Proof. exact (MK_COMB (@lem3482754) (@lem3482713 A f s x)). Qed.
Lemma lem3482756 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term459 A f s x) = (term460 A f s x).
Proof. exact (MK_COMB (@lem3482755 A f s x) (@lem3482747 A f s x)). Qed.
Lemma lem3482757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3482758 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term461 A f s x) = (term462 A f s x).
Proof. exact (MK_COMB (@lem3482757) (@lem3482756 A f s x)). Qed.
Lemma lem3482759 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term463 A f s x) = (term464 A f s x).
Proof. exact (MK_COMB (@lem3482758 A f s x) (@lem3482753 A f s x)). Qed.
Lemma lem3482760 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term432 A f s x) = (term463 A f s x).
Proof. exact (@lem17646 (term395 A f s x) (term412 A f s x)). Qed.
Lemma lem3482761 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term432 A f s x) = (term464 A f s x).
Proof. exact (TRANS (@lem3482760 A f s x) (@lem3482759 A f s x)). Qed.
Lemma lem3482916 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3482917 {A : Type'} (P : Prop) (Q : type686 A) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem3482916 (A -> Prop) P Q). Qed.
Lemma lem3482918 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term465 A f s x) = (term466 A f s x).
Proof. exact (@lem3482917 A (term439 A f s x) (term449 A f s x)). Qed.
Lemma lem3482919 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term467 A f s x t) = (term441 A f t s x).
Proof. exact (eq_refl (term467 A f s x t)). Qed.
Lemma lem3482920 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term468 A f s x) = (term449 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482919 A f t s x)). Qed.
Lemma lem3482921 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482922 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term469 A f s x) = (term450 A f s x).
Proof. exact (MK_COMB (@lem3482921 A) (@lem3482920 A f s x)). Qed.
Lemma lem3482923 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term458 A f s x) = (term458 A f s x).
Proof. exact (eq_refl (term458 A f s x)). Qed.
Lemma lem3482924 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term465 A f s x) = (term460 A f s x).
Proof. exact (MK_COMB (@lem3482923 A f s x) (@lem3482922 A f s x)). Qed.
Lemma lem3482925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482926 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term470 A f s x) = (term471 A f s x).
Proof. exact (MK_COMB (@lem3482925) (@lem3482924 A f s x)). Qed.
Lemma lem3482927 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term467 A f s x t) = (term441 A f t s x).
Proof. exact (eq_refl (term467 A f s x t)). Qed.
Lemma lem3482928 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term458 A f s x) = (term458 A f s x).
Proof. exact (eq_refl (term458 A f s x)). Qed.
Lemma lem3482929 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term472 A f s x t) = (term473 A f t s x).
Proof. exact (MK_COMB (@lem3482928 A f s x) (@lem3482927 A f t s x)). Qed.
Lemma lem3482930 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term474 A f s x) = (term475 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482929 A f t s x)). Qed.
Lemma lem3482931 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482932 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term466 A f s x) = (term476 A f s x).
Proof. exact (MK_COMB (@lem3482931 A) (@lem3482930 A f s x)). Qed.
Lemma lem3482933 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term465 A f s x) = (term466 A f s x)) = ((term460 A f s x) = (term476 A f s x)).
Proof. exact (MK_COMB (@lem3482926 A f s x) (@lem3482932 A f s x)). Qed.
Lemma lem3482934 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term460 A f s x) = (term476 A f s x).
Proof. exact (EQ_MP (@lem3482933 A f s x) (@lem3482918 A f s x)). Qed.
Lemma lem3482935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3482936 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term462 A f s x) = (term477 A f s x).
Proof. exact (MK_COMB (@lem3482935) (@lem3482934 A f s x)). Qed.
Lemma lem3482938 {A : Type'} (P : A -> Prop) (Q : Prop) : (term478 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3482939 {A : Type'} (P : type686 A) (Q : Prop) : (term480 A P Q) = (term481 A P Q).
Proof. exact (@lem3482938 (A -> Prop) P Q). Qed.
Lemma lem3482940 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term482 A f s x) = (term483 A f s x).
Proof. exact (@lem3482939 A (term221 A f x) (term281 A s x)). Qed.
Lemma lem3482941 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term282 A f x t) = (term214 A f t x).
Proof. exact (eq_refl (term282 A f x t)). Qed.
Lemma lem3482942 {A : Type'} (f : type686 A) (x : A) : (term283 A f x) = (term221 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482941 A f t x)). Qed.
Lemma lem3482943 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482944 {A : Type'} (f : type686 A) (x : A) : (term284 A f x) = (term222 A f x).
Proof. exact (MK_COMB (@lem3482943 A) (@lem3482942 A f x)). Qed.
Lemma lem3482945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3482946 {A : Type'} (f : type686 A) (x : A) : (term484 A f x) = (term434 A f x).
Proof. exact (MK_COMB (@lem3482945) (@lem3482944 A f x)). Qed.
Lemma lem3482947 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term281 A s x).
Proof. exact (eq_refl (term281 A s x)). Qed.
Lemma lem3482948 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term482 A f s x) = (term436 A f s x).
Proof. exact (MK_COMB (@lem3482946 A f x) (@lem3482947 A s x)). Qed.
Lemma lem3482949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482950 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term485 A f s x) = (term486 A f s x).
Proof. exact (MK_COMB (@lem3482949) (@lem3482948 A f s x)). Qed.
Lemma lem3482951 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term282 A f x t) = (term214 A f t x).
Proof. exact (eq_refl (term282 A f x t)). Qed.
Lemma lem3482952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3482953 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term487 A f x t) = (term488 A f t x).
Proof. exact (MK_COMB (@lem3482952) (@lem3482951 A f t x)). Qed.
Lemma lem3482954 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term281 A s x).
Proof. exact (eq_refl (term281 A s x)). Qed.
Lemma lem3482955 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term489 A f t s x) = (term490 A f t s x).
Proof. exact (MK_COMB (@lem3482953 A f t x) (@lem3482954 A s x)). Qed.
Lemma lem3482956 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term491 A f s x) = (term492 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482955 A f t s x)). Qed.
Lemma lem3482957 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482958 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term483 A f s x) = (term493 A f s x).
Proof. exact (MK_COMB (@lem3482957 A) (@lem3482956 A f s x)). Qed.
Lemma lem3482959 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term482 A f s x) = (term483 A f s x)) = ((term436 A f s x) = (term493 A f s x)).
Proof. exact (MK_COMB (@lem3482950 A f s x) (@lem3482958 A f s x)). Qed.
Lemma lem3482960 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term436 A f s x) = (term493 A f s x).
Proof. exact (EQ_MP (@lem3482959 A f s x) (@lem3482940 A f s x)). Qed.
Lemma lem3482961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482962 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term454 A f s x) = (term494 A f s x).
Proof. exact (MK_COMB (@lem3482961) (@lem3482960 A f s x)). Qed.
Lemma lem3482963 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term452 A f s x) = (term452 A f s x).
Proof. exact (eq_refl (term452 A f s x)). Qed.
Lemma lem3482964 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term456 A f s x) = (term495 A f s x).
Proof. exact (MK_COMB (@lem3482962 A f s x) (@lem3482963 A f s x)). Qed.
Lemma lem3482966 {A : Type'} (P : A -> Prop) (Q : Prop) : (term294 A P Q) = (term295 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3482967 {A : Type'} (P : type686 A) (Q : Prop) : (term296 A P Q) = (term297 A P Q).
Proof. exact (@lem3482966 (A -> Prop) P Q). Qed.
Lemma lem3482968 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term496 A f s x) = (term497 A f s x).
Proof. exact (@lem3482967 A (term492 A f s x) (term452 A f s x)). Qed.
Lemma lem3482969 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term498 A f s x t) = (term490 A f t s x).
Proof. exact (eq_refl (term498 A f s x t)). Qed.
Lemma lem3482970 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term499 A f s x) = (term492 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482969 A f t s x)). Qed.
Lemma lem3482971 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482972 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term500 A f s x) = (term493 A f s x).
Proof. exact (MK_COMB (@lem3482971 A) (@lem3482970 A f s x)). Qed.
Lemma lem3482973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482974 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term501 A f s x) = (term494 A f s x).
Proof. exact (MK_COMB (@lem3482973) (@lem3482972 A f s x)). Qed.
Lemma lem3482975 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term452 A f s x) = (term452 A f s x).
Proof. exact (eq_refl (term452 A f s x)). Qed.
Lemma lem3482976 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term496 A f s x) = (term495 A f s x).
Proof. exact (MK_COMB (@lem3482974 A f s x) (@lem3482975 A f s x)). Qed.
Lemma lem3482977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3482978 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term502 A f s x) = (term503 A f s x).
Proof. exact (MK_COMB (@lem3482977) (@lem3482976 A f s x)). Qed.
Lemma lem3482979 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term498 A f s x t) = (term490 A f t s x).
Proof. exact (eq_refl (term498 A f s x t)). Qed.
Lemma lem3482980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3482981 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term504 A f s x t) = (term505 A f t s x).
Proof. exact (MK_COMB (@lem3482980) (@lem3482979 A f t s x)). Qed.
Lemma lem3482982 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term452 A f s x) = (term452 A f s x).
Proof. exact (eq_refl (term452 A f s x)). Qed.
Lemma lem3482983 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term506 A t f s x) = (term507 A t f s x).
Proof. exact (MK_COMB (@lem3482981 A f t s x) (@lem3482982 A f s x)). Qed.
Lemma lem3482984 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term508 A f s x) = (term509 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482983 A t f s x)). Qed.
Lemma lem3482985 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482986 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term497 A f s x) = (term510 A f s x).
Proof. exact (MK_COMB (@lem3482985 A) (@lem3482984 A f s x)). Qed.
Lemma lem3482987 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term496 A f s x) = (term497 A f s x)) = ((term495 A f s x) = (term510 A f s x)).
Proof. exact (MK_COMB (@lem3482978 A f s x) (@lem3482986 A f s x)). Qed.
Lemma lem3482988 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term495 A f s x) = (term510 A f s x).
Proof. exact (EQ_MP (@lem3482987 A f s x) (@lem3482968 A f s x)). Qed.
Lemma lem3482989 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term456 A f s x) = (term510 A f s x).
Proof. exact (TRANS (@lem3482964 A f s x) (@lem3482988 A f s x)). Qed.
Lemma lem3482990 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term464 A f s x) = (term511 A f s x).
Proof. exact (MK_COMB (@lem3482936 A f s x) (@lem3482989 A f s x)). Qed.
Lemma lem3482992 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term314 A P Q) = (term315 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3482993 {A : Type'} (P : type686 A) (Q : type686 A) : (term316 A P Q) = (term317 A P Q).
Proof. exact (@lem3482992 (A -> Prop) P Q). Qed.
Lemma lem3482994 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term512 A f s x) = (term513 A f s x).
Proof. exact (@lem3482993 A (term475 A f s x) (term509 A f s x)). Qed.
Lemma lem3482995 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term514 A f s x t) = (term473 A f t s x).
Proof. exact (eq_refl (term514 A f s x t)). Qed.
Lemma lem3482996 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term515 A f s x) = (term475 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3482995 A f t s x)). Qed.
Lemma lem3482997 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3482998 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term516 A f s x) = (term476 A f s x).
Proof. exact (MK_COMB (@lem3482997 A) (@lem3482996 A f s x)). Qed.
Lemma lem3482999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483000 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term517 A f s x) = (term477 A f s x).
Proof. exact (MK_COMB (@lem3482999) (@lem3482998 A f s x)). Qed.
Lemma lem3483001 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term518 A f s x t) = (term507 A t f s x).
Proof. exact (eq_refl (term518 A f s x t)). Qed.
Lemma lem3483002 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term519 A f s x) = (term509 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483001 A t f s x)). Qed.
Lemma lem3483003 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3483004 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term520 A f s x) = (term510 A f s x).
Proof. exact (MK_COMB (@lem3483003 A) (@lem3483002 A f s x)). Qed.
Lemma lem3483005 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term512 A f s x) = (term511 A f s x).
Proof. exact (MK_COMB (@lem3483000 A f s x) (@lem3483004 A f s x)). Qed.
Lemma lem3483006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483007 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term521 A f s x) = (term522 A f s x).
Proof. exact (MK_COMB (@lem3483006) (@lem3483005 A f s x)). Qed.
Lemma lem3483008 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term514 A f s x t) = (term473 A f t s x).
Proof. exact (eq_refl (term514 A f s x t)). Qed.
Lemma lem3483009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483010 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term523 A f s x t) = (term524 A f t s x).
Proof. exact (MK_COMB (@lem3483009) (@lem3483008 A f t s x)). Qed.
Lemma lem3483011 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term518 A f s x t) = (term507 A t f s x).
Proof. exact (eq_refl (term518 A f s x t)). Qed.
Lemma lem3483012 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term525 A f s x t) = (term526 A t f s x).
Proof. exact (MK_COMB (@lem3483010 A f t s x) (@lem3483011 A t f s x)). Qed.
Lemma lem3483013 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term527 A f s x) = (term528 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483012 A t f s x)). Qed.
Lemma lem3483014 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3483015 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term513 A f s x) = (term529 A f s x).
Proof. exact (MK_COMB (@lem3483014 A) (@lem3483013 A f s x)). Qed.
Lemma lem3483016 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term512 A f s x) = (term513 A f s x)) = ((term511 A f s x) = (term529 A f s x)).
Proof. exact (MK_COMB (@lem3483007 A f s x) (@lem3483015 A f s x)). Qed.
Lemma lem3483017 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term511 A f s x) = (term529 A f s x).
Proof. exact (EQ_MP (@lem3483016 A f s x) (@lem3482994 A f s x)). Qed.
Lemma lem3483019 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term464 A f s x) = (term529 A f s x).
Proof. exact (TRANS (@lem3482990 A f s x) (@lem3483017 A f s x)). Qed.
Lemma lem3483020 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term432 A f s x) = (term529 A f s x).
Proof. exact (TRANS (@lem3482761 A f s x) (@lem3483019 A f s x)). Qed.
Lemma lem3483021 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term432 A f s x) : term529 A f s x.
Proof. exact (EQ_MP (@lem3483020 A f s x) (@lem3482654 A f s x h1)). Qed.
Lemma lem3483022 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term526 A t f s x) : term526 A t f s x.
Proof. exact (h1). Qed.
Lemma lem3483023 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : f x'.
Proof. exact (h1). Qed.
Lemma lem3483028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483029 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483028 A Prop f x). Qed.
Lemma lem3483031 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483029 A s x). Qed.
Lemma lem3483036 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483037 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483036 A Prop f x). Qed.
Lemma lem3483039 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483037 A t x). Qed.
Lemma lem3483040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483041 {A : Type'} (t : A -> Prop) (x : A) : (term153 A t x) = (term336 A t x).
Proof. exact (MK_COMB (@lem3483040) (@lem3483039 A t x)). Qed.
Lemma lem3483042 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term178 A t s x) = (term337 A t s x).
Proof. exact (MK_COMB (@lem3483041 A t x) (@lem3483031 A s x)). Qed.
Lemma lem3483043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483048 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483049 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3483048 (A -> Prop) Prop f x). Qed.
Lemma lem3483051 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483049 A f t). Qed.
Lemma lem3483052 {A : Type'} (f : type686 A) (t : A -> Prop) : (term143 A f t) = (term338 A f t).
Proof. exact (MK_COMB (@lem3483043) (@lem3483051 A f t)). Qed.
Lemma lem3483053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483054 {A : Type'} (f : type686 A) (t : A -> Prop) : (term339 A f t) = (term340 A f t).
Proof. exact (MK_COMB (@lem3483053) (@lem3483052 A f t)). Qed.
Lemma lem3483055 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term443 A f t s x) = (term530 A f t s x).
Proof. exact (MK_COMB (@lem3483054 A f t) (@lem3483042 A t s x)). Qed.
Lemma lem3483056 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term451 A f s x) = (term531 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483055 A f t s x)). Qed.
Lemma lem3483057 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3483058 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term452 A f s x) = (term532 A f s x).
Proof. exact (MK_COMB (@lem3483057 A) (@lem3483056 A f s x)). Qed.
Lemma lem3483059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483065 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483064 A Prop f x). Qed.
Lemma lem3483067 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483065 A s x). Qed.
Lemma lem3483068 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3483059) (@lem3483067 A s x)). Qed.
Lemma lem3483069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483074 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483075 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483074 A Prop f x). Qed.
Lemma lem3483077 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483075 A t x). Qed.
Lemma lem3483078 {A : Type'} (t : A -> Prop) (x : A) : (term281 A t x) = (term344 A t x).
Proof. exact (MK_COMB (@lem3483069) (@lem3483077 A t x)). Qed.
Lemma lem3483083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483084 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3483083 (A -> Prop) Prop f x). Qed.
Lemma lem3483086 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483084 A f t). Qed.
Lemma lem3483087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483088 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term345 A f t).
Proof. exact (MK_COMB (@lem3483087) (@lem3483086 A f t)). Qed.
Lemma lem3483089 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term214 A f t x) = (term346 A f t x).
Proof. exact (MK_COMB (@lem3483088 A f t) (@lem3483078 A t x)). Qed.
Lemma lem3483090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483091 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term488 A f t x) = (term533 A f t x).
Proof. exact (MK_COMB (@lem3483090) (@lem3483089 A f t x)). Qed.
Lemma lem3483092 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term490 A f t s x) = (term534 A f t s x).
Proof. exact (MK_COMB (@lem3483091 A f t x) (@lem3483068 A s x)). Qed.
Lemma lem3483093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483094 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term505 A f t s x) = (term535 A f t s x).
Proof. exact (MK_COMB (@lem3483093) (@lem3483092 A f t s x)). Qed.
Lemma lem3483095 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term507 A t f s x) = (term536 A t f s x).
Proof. exact (MK_COMB (@lem3483094 A f t s x) (@lem3483058 A f s x)). Qed.
Lemma lem3483096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483102 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483101 A Prop f x). Qed.
Lemma lem3483104 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483102 A s x). Qed.
Lemma lem3483105 {A : Type'} (s : A -> Prop) (x : A) : (term281 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3483096) (@lem3483104 A s x)). Qed.
Lemma lem3483106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483112 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483111 A Prop f x). Qed.
Lemma lem3483114 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483112 A t x). Qed.
Lemma lem3483115 {A : Type'} (t : A -> Prop) (x : A) : (term281 A t x) = (term344 A t x).
Proof. exact (MK_COMB (@lem3483106) (@lem3483114 A t x)). Qed.
Lemma lem3483116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483117 {A : Type'} (t : A -> Prop) (x : A) : (term225 A t x) = (term347 A t x).
Proof. exact (MK_COMB (@lem3483116) (@lem3483115 A t x)). Qed.
Lemma lem3483118 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term231 A t s x) = (term351 A t s x).
Proof. exact (MK_COMB (@lem3483117 A t x) (@lem3483105 A s x)). Qed.
Lemma lem3483123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483124 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3483123 (A -> Prop) Prop f x). Qed.
Lemma lem3483126 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483124 A f t). Qed.
Lemma lem3483127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483128 {A : Type'} (f : type686 A) (t : A -> Prop) : (term232 A f t) = (term345 A f t).
Proof. exact (MK_COMB (@lem3483127) (@lem3483126 A f t)). Qed.
Lemma lem3483129 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term441 A f t s x) = (term537 A f t s x).
Proof. exact (MK_COMB (@lem3483128 A f t) (@lem3483118 A t s x)). Qed.
Lemma lem3483134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483135 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483134 A Prop f x). Qed.
Lemma lem3483137 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483135 A s x). Qed.
Lemma lem3483142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483143 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3483142 A Prop f x). Qed.
Lemma lem3483145 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483143 A t x). Qed.
Lemma lem3483146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3483151 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483152 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3483151 (A -> Prop) Prop f x). Qed.
Lemma lem3483154 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483152 A f t). Qed.
Lemma lem3483155 {A : Type'} (f : type686 A) (t : A -> Prop) : (term143 A f t) = (term338 A f t).
Proof. exact (MK_COMB (@lem3483146) (@lem3483154 A f t)). Qed.
Lemma lem3483156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483157 {A : Type'} (f : type686 A) (t : A -> Prop) : (term339 A f t) = (term340 A f t).
Proof. exact (MK_COMB (@lem3483156) (@lem3483155 A f t)). Qed.
Lemma lem3483158 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term215 A f t x) = (term353 A f t x).
Proof. exact (MK_COMB (@lem3483157 A f t) (@lem3483145 A t x)). Qed.
Lemma lem3483159 {A : Type'} (f : type686 A) (x : A) : (term223 A f x) = (term354 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483158 A f t x)). Qed.
Lemma lem3483160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3483161 {A : Type'} (f : type686 A) (x : A) : (term224 A f x) = (term355 A f x).
Proof. exact (MK_COMB (@lem3483160 A) (@lem3483159 A f x)). Qed.
Lemma lem3483162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483163 {A : Type'} (f : type686 A) (x : A) : (term438 A f x) = (term538 A f x).
Proof. exact (MK_COMB (@lem3483162) (@lem3483161 A f x)). Qed.
Lemma lem3483164 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term439 A f s x) = (term539 A f s x).
Proof. exact (MK_COMB (@lem3483163 A f x) (@lem3483137 A s x)). Qed.
Lemma lem3483165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3483166 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term458 A f s x) = (term540 A f s x).
Proof. exact (MK_COMB (@lem3483165) (@lem3483164 A f s x)). Qed.
Lemma lem3483167 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term473 A f t s x) = (term541 A f t s x).
Proof. exact (MK_COMB (@lem3483166 A f s x) (@lem3483129 A f t s x)). Qed.
Lemma lem3483168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3483169 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term524 A f t s x) = (term542 A f t s x).
Proof. exact (MK_COMB (@lem3483168) (@lem3483167 A f t s x)). Qed.
Lemma lem3483170 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term526 A t f s x) = (term543 A t f s x).
Proof. exact (MK_COMB (@lem3483169 A f t s x) (@lem3483095 A t f s x)). Qed.
Lemma lem3483171 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term526 A t f s x) : term543 A t f s x.
Proof. exact (EQ_MP (@lem3483170 A t f s x) (@lem3483022 A t f s x h1)). Qed.
Lemma lem3483176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3483177 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3483176 (A -> Prop) Prop f x). Qed.
Lemma lem3483179 {A : Type'} (f : type686 A) (x' : A -> Prop) : (f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3483177 A f x'). Qed.
Lemma lem3483181 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term541 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3483182 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term536 A t f s x.
Proof. exact (h1). Qed.
Lemma lem3483183 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term537 A f t s x.
Proof. exact (proj2 (@lem3483181 A f t s x h1)). Qed.
Lemma lem3483184 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term539 A f s x.
Proof. exact (proj1 (@lem3483181 A f t s x h1)). Qed.
Lemma lem3483185 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term351 A t s x.
Proof. exact (proj2 (@lem3483183 A f t s x h1)). Qed.
Lemma lem3483188 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term355 A f x.
Proof. exact (proj1 (@lem3483184 A f t s x h1)). Qed.
Lemma lem3483191 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term532 A f s x.
Proof. exact (proj2 (@lem3483182 A t f s x h1)). Qed.
Lemma lem3483192 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term534 A f t s x.
Proof. exact (proj1 (@lem3483182 A t f s x h1)). Qed.
Lemma lem3483193 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term346 A f t x.
Proof. exact (h1). Qed.
Lemma lem3483212 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term353 A f t x) = (term353 A f t x).
Proof. exact (eq_refl (term353 A f t x)). Qed.
Lemma lem3483213 {A : Type'} (f : type686 A) (x : A) : (term354 A f x) = (term354 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483212 A f t x)). Qed.
Lemma lem3483214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3483216 {A : Type'} (f : type686 A) (x : A) : (term355 A f x) = (term355 A f x).
Proof. exact (MK_COMB (@lem3483214 A) (@lem3483213 A f x)). Qed.
Lemma lem3483217 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term355 A f x.
Proof. exact (EQ_MP (@lem3483216 A f x) (@lem3483188 A f t s x h1)). Qed.
Lemma lem3483225 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term344 A t x.
Proof. exact (h1). Qed.
Lemma lem3483254 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3483276 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term530 A f t s x) = (term544 A f t s x).
Proof. exact (@lem19490 (@I (A -> Prop) t x) (term338 A f t) (@I (A -> Prop) s x)). Qed.
Lemma lem3483277 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term531 A f s x) = (term545 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483276 A f t s x)). Qed.
Lemma lem3483278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3483280 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term532 A f s x) = (term546 A f s x).
Proof. exact (MK_COMB (@lem3483278 A) (@lem3483277 A f s x)). Qed.
Lemma lem3483281 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term546 A f s x.
Proof. exact (EQ_MP (@lem3483280 A f s x) (@lem3483191 A t f s x h1)). Qed.
Lemma lem3483311 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term530 A f t s x) = (term544 A f t s x).
Proof. exact (@lem19490 (@I (A -> Prop) t x) (term338 A f t) (@I (A -> Prop) s x)). Qed.
Lemma lem3483312 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term531 A f s x) = (term545 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3483311 A f t s x)). Qed.
Lemma lem3483313 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3483315 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term532 A f s x) = (term546 A f s x).
Proof. exact (MK_COMB (@lem3483313 A) (@lem3483312 A f s x)). Qed.
Lemma lem3483316 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term546 A f s x.
Proof. exact (EQ_MP (@lem3483315 A f s x) (@lem3483191 A t f s x h1)). Qed.
Lemma lem3483320 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3483321 {A : Type'} (_36707 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term364 A f x _36707.
Proof. exact (@lem3483217 A f t s x h1 _36707). Qed.
Lemma lem3483322 {A : Type'} (f : type686 A) (_36707 : A -> Prop) (x : A) : (term364 A f x _36707) = (term353 A f _36707 x).
Proof. exact (eq_refl (term364 A f x _36707)). Qed.
Lemma lem3483327 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term547 A f s x _36709.
Proof. exact (@lem3483281 A t f s x h1 _36709). Qed.
Lemma lem3483328 {A : Type'} (f : type686 A) (_36709 : A -> Prop) (s : A -> Prop) (x : A) : (term547 A f s x _36709) = (term544 A f _36709 s x).
Proof. exact (eq_refl (term547 A f s x _36709)). Qed.
Lemma lem3483329 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term544 A f _36709 s x.
Proof. exact (EQ_MP (@lem3483328 A f _36709 s x) (@lem3483327 A _36709 t f s x h1)). Qed.
Lemma lem3483330 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term547 A f s x _36710.
Proof. exact (@lem3483316 A t f s x h1 _36710). Qed.
Lemma lem3483331 {A : Type'} (f : type686 A) (_36710 : A -> Prop) (s : A -> Prop) (x : A) : (term547 A f s x _36710) = (term544 A f _36710 s x).
Proof. exact (eq_refl (term547 A f s x _36710)). Qed.
Lemma lem3483332 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term544 A f _36710 s x.
Proof. exact (EQ_MP (@lem3483331 A f _36710 s x) (@lem3483330 A _36710 t f s x h1)). Qed.
Lemma lem3483346 {A : Type'} (_36707 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term353 A f _36707 x.
Proof. exact (EQ_MP (@lem3483322 A f _36707 x) (@lem3483321 A _36707 f t s x h1)). Qed.
Lemma lem3483350 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term344 A t x.
Proof. exact (h1). Qed.
Lemma lem3483364 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3483370 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term344 A t x.
Proof. exact (proj2 (@lem3483193 A f t x h1)). Qed.
Lemma lem3483376 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term353 A f _36709 x.
Proof. exact (proj1 (@lem3483329 A _36709 t f s x h1)). Qed.
Lemma lem3483386 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term344 A s x.
Proof. exact (h1). Qed.
Lemma lem3483398 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term366 A f _36710 s x.
Proof. exact (proj2 (@lem3483332 A _36710 t f s x h1)). Qed.
Lemma lem3483400 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3483183 A f t s x h1)). Qed.
Lemma lem3483401 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term371 A f t.
Proof. exact (fun h0 : term338 A f t => @lem3483400 A f t s x h1). Qed.
Lemma lem3483403 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483404 {A : Type'} (f : type686 A) (t : A -> Prop) : (term371 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483403 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3483405 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3483404 A f t) (@lem3483401 A f t s x h1)). Qed.
Lemma lem3483411 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3483412 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : (term353 A f _36707 x) = (term372 A x f _36707).
Proof. exact (@lem3483411 (@I (A -> Prop) _36707 x) (term338 A f _36707)). Qed.
Lemma lem3483418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483419 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : (term373 A f _36707 x) = (term374 A x f _36707).
Proof. exact (MK_COMB (@lem3483418) (@lem3483412 A x f _36707)). Qed.
Lemma lem3483425 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : (term372 A x f _36707) = (term372 A x f _36707).
Proof. exact (eq_refl (term372 A x f _36707)). Qed.
Lemma lem3483426 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : ((term353 A f _36707 x) = (term372 A x f _36707)) = ((term372 A x f _36707) = (term372 A x f _36707)).
Proof. exact (MK_COMB (@lem3483419 A x f _36707) (@lem3483425 A x f _36707)). Qed.
Lemma lem3483428 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3483429 (x : Prop) : (x = x) = True.
Proof. exact (@lem3483428 Prop x). Qed.
Lemma lem3483430 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : ((term372 A x f _36707) = (term372 A x f _36707)) = True.
Proof. exact (@lem3483429 (term372 A x f _36707)). Qed.
Lemma lem3483431 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : ((term353 A f _36707 x) = (term372 A x f _36707)) = True.
Proof. exact (TRANS (@lem3483426 A x f _36707) (@lem3483430 A x f _36707)). Qed.
Lemma lem3483432 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : True = ((term353 A f _36707 x) = (term372 A x f _36707)).
Proof. exact (SYM (@lem3483431 A x f _36707)). Qed.
Lemma lem3483433 {A : Type'} (x : A) (f : type686 A) (_36707 : A -> Prop) : (term353 A f _36707 x) = (term372 A x f _36707).
Proof. exact (EQ_MP (@lem3483432 A x f _36707) (@lem0)). Qed.
Lemma lem3483434 {A : Type'} (_36707 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term372 A x f _36707.
Proof. exact (EQ_MP (@lem3483433 A x f _36707) (@lem3483346 A _36707 f t s x h1)). Qed.
Lemma lem3483436 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3483437 {A : Type'} (f : type686 A) (_36707 : A -> Prop) (x : A) : (term372 A x f _36707) = (term376 A f _36707 x).
Proof. exact (@lem3483436 (term338 A f _36707) (@I (A -> Prop) _36707 x)). Qed.
Lemma lem3483439 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3483440 {A : Type'} (f : type686 A) (_36707 : A -> Prop) : (term377 A f _36707) = (@I ((A -> Prop) -> Prop) f _36707).
Proof. exact (@lem3483439 (@I ((A -> Prop) -> Prop) f _36707)). Qed.
Lemma lem3483441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3483442 {A : Type'} (f : type686 A) (_36707 : A -> Prop) : (term378 A f _36707) = (term379 A f _36707).
Proof. exact (MK_COMB (@lem3483441) (@lem3483440 A f _36707)). Qed.
Lemma lem3483443 {A : Type'} (_36707 : A -> Prop) (x : A) : (@I (A -> Prop) _36707 x) = (@I (A -> Prop) _36707 x).
Proof. exact (eq_refl (@I (A -> Prop) _36707 x)). Qed.
Lemma lem3483444 {A : Type'} (f : type686 A) (_36707 : A -> Prop) (x : A) : (term376 A f _36707 x) = (term380 A f _36707 x).
Proof. exact (MK_COMB (@lem3483442 A f _36707) (@lem3483443 A _36707 x)). Qed.
Lemma lem3483445 {A : Type'} (f : type686 A) (_36707 : A -> Prop) (x : A) : (term372 A x f _36707) = (term380 A f _36707 x).
Proof. exact (TRANS (@lem3483437 A f _36707 x) (@lem3483444 A f _36707 x)). Qed.
Lemma lem3483448 {A : Type'} (_36707 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term380 A f _36707 x.
Proof. exact (EQ_MP (@lem3483445 A f _36707 x) (@lem3483434 A _36707 f t s x h1)). Qed.
Lemma lem3483449 {A : Type'} (_36707 : A -> Prop) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term380 A f _36707 x.
Proof. exact (@lem3483448 A _36707 f t s x h1). Qed.
Lemma lem3483450 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term380 A f t x.
Proof. exact (@lem3483449 A t f t s x h1). Qed.
Lemma lem3483453 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I (A -> Prop) t x.
Proof. exact (@lem3483450 A f t s x h1 (@lem3483405 A f t s x h1)). Qed.
Lemma lem3483454 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term367 A t x.
Proof. exact (fun h0 : term344 A t x => @lem3483453 A f t s x h1). Qed.
Lemma lem3483456 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483457 {A : Type'} (t : A -> Prop) (x : A) : (term367 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483456 (@I (A -> Prop) t x)). Qed.
Lemma lem3483458 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3483457 A t x) (@lem3483454 A f t s x h1)). Qed.
Lemma lem3483461 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3483463 {A : Type'} (t : A -> Prop) (x : A) : (term344 A t x) = (term369 A t x).
Proof. exact (@lem3483461 (@I (A -> Prop) t x)). Qed.
Lemma lem3483466 {A : Type'} (t : A -> Prop) (x : A) (h1 : term344 A t x) : term369 A t x.
Proof. exact (EQ_MP (@lem3483463 A t x) (@lem3483350 A t x h1)). Qed.
Lemma lem3483469 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : False.
Proof. exact (@lem3483466 A t x h1 (@lem3483458 A f t s x h2)). Qed.
Lemma lem3483470 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3483469 A f t s x h1 h2). Qed.
Lemma lem3483472 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483473 : term370 = False.
Proof. exact (@lem3483472 False). Qed.
Lemma lem3483474 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483473) (@lem3483470 A f t s x h1 h2)). Qed.
Lemma lem3483476 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3483184 A f t s x h1)). Qed.
Lemma lem3483477 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : term367 A s x.
Proof. exact (fun h0 : term344 A s x => @lem3483476 A f t s x h1). Qed.
Lemma lem3483479 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483480 {A : Type'} (s : A -> Prop) (x : A) : (term367 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483479 (@I (A -> Prop) s x)). Qed.
Lemma lem3483481 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3483480 A s x) (@lem3483477 A f t s x h1)). Qed.
Lemma lem3483484 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3483486 {A : Type'} (s : A -> Prop) (x : A) : (term344 A s x) = (term369 A s x).
Proof. exact (@lem3483484 (@I (A -> Prop) s x)). Qed.
Lemma lem3483489 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term369 A s x.
Proof. exact (EQ_MP (@lem3483486 A s x) (@lem3483364 A s x h1)). Qed.
Lemma lem3483492 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : False.
Proof. exact (@lem3483489 A s x h1 (@lem3483481 A f t s x h2)). Qed.
Lemma lem3483493 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3483492 A f t s x h1 h2). Qed.
Lemma lem3483495 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483496 : term370 = False.
Proof. exact (@lem3483495 False). Qed.
Lemma lem3483497 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483496) (@lem3483493 A f t s x h1 h2)). Qed.
Lemma lem3483499 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3483193 A f t x h1)). Qed.
Lemma lem3483500 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term371 A f t.
Proof. exact (fun h0 : term338 A f t => @lem3483499 A f t x h1). Qed.
Lemma lem3483502 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483503 {A : Type'} (f : type686 A) (t : A -> Prop) : (term371 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3483502 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3483504 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3483503 A f t) (@lem3483500 A f t x h1)). Qed.
Lemma lem3483510 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3483511 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : (term353 A f _36709 x) = (term372 A x f _36709).
Proof. exact (@lem3483510 (@I (A -> Prop) _36709 x) (term338 A f _36709)). Qed.
Lemma lem3483517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483518 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : (term373 A f _36709 x) = (term374 A x f _36709).
Proof. exact (MK_COMB (@lem3483517) (@lem3483511 A x f _36709)). Qed.
Lemma lem3483524 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : (term372 A x f _36709) = (term372 A x f _36709).
Proof. exact (eq_refl (term372 A x f _36709)). Qed.
Lemma lem3483525 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : ((term353 A f _36709 x) = (term372 A x f _36709)) = ((term372 A x f _36709) = (term372 A x f _36709)).
Proof. exact (MK_COMB (@lem3483518 A x f _36709) (@lem3483524 A x f _36709)). Qed.
Lemma lem3483527 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3483528 (x : Prop) : (x = x) = True.
Proof. exact (@lem3483527 Prop x). Qed.
Lemma lem3483529 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : ((term372 A x f _36709) = (term372 A x f _36709)) = True.
Proof. exact (@lem3483528 (term372 A x f _36709)). Qed.
Lemma lem3483530 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : ((term353 A f _36709 x) = (term372 A x f _36709)) = True.
Proof. exact (TRANS (@lem3483525 A x f _36709) (@lem3483529 A x f _36709)). Qed.
Lemma lem3483531 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : True = ((term353 A f _36709 x) = (term372 A x f _36709)).
Proof. exact (SYM (@lem3483530 A x f _36709)). Qed.
Lemma lem3483532 {A : Type'} (x : A) (f : type686 A) (_36709 : A -> Prop) : (term353 A f _36709 x) = (term372 A x f _36709).
Proof. exact (EQ_MP (@lem3483531 A x f _36709) (@lem0)). Qed.
Lemma lem3483533 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term372 A x f _36709.
Proof. exact (EQ_MP (@lem3483532 A x f _36709) (@lem3483376 A _36709 t f s x h1)). Qed.
Lemma lem3483535 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3483536 {A : Type'} (f : type686 A) (_36709 : A -> Prop) (x : A) : (term372 A x f _36709) = (term376 A f _36709 x).
Proof. exact (@lem3483535 (term338 A f _36709) (@I (A -> Prop) _36709 x)). Qed.
Lemma lem3483538 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3483539 {A : Type'} (f : type686 A) (_36709 : A -> Prop) : (term377 A f _36709) = (@I ((A -> Prop) -> Prop) f _36709).
Proof. exact (@lem3483538 (@I ((A -> Prop) -> Prop) f _36709)). Qed.
Lemma lem3483540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3483541 {A : Type'} (f : type686 A) (_36709 : A -> Prop) : (term378 A f _36709) = (term379 A f _36709).
Proof. exact (MK_COMB (@lem3483540) (@lem3483539 A f _36709)). Qed.
Lemma lem3483542 {A : Type'} (_36709 : A -> Prop) (x : A) : (@I (A -> Prop) _36709 x) = (@I (A -> Prop) _36709 x).
Proof. exact (eq_refl (@I (A -> Prop) _36709 x)). Qed.
Lemma lem3483543 {A : Type'} (f : type686 A) (_36709 : A -> Prop) (x : A) : (term376 A f _36709 x) = (term380 A f _36709 x).
Proof. exact (MK_COMB (@lem3483541 A f _36709) (@lem3483542 A _36709 x)). Qed.
Lemma lem3483544 {A : Type'} (f : type686 A) (_36709 : A -> Prop) (x : A) : (term372 A x f _36709) = (term380 A f _36709 x).
Proof. exact (TRANS (@lem3483536 A f _36709 x) (@lem3483543 A f _36709 x)). Qed.
Lemma lem3483547 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term380 A f _36709 x.
Proof. exact (EQ_MP (@lem3483544 A f _36709 x) (@lem3483533 A _36709 t f s x h1)). Qed.
Lemma lem3483548 {A : Type'} (_36709 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term380 A f _36709 x.
Proof. exact (@lem3483547 A _36709 t f s x h1). Qed.
Lemma lem3483549 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term380 A f t x.
Proof. exact (@lem3483548 A t t f s x h1). Qed.
Lemma lem3483552 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : @I (A -> Prop) t x.
Proof. exact (@lem3483549 A t f s x h2 (@lem3483504 A f t x h1)). Qed.
Lemma lem3483553 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : term367 A t x.
Proof. exact (fun h0 : term344 A t x => @lem3483552 A t f s x h1 h2). Qed.
Lemma lem3483555 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483556 {A : Type'} (t : A -> Prop) (x : A) : (term367 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3483555 (@I (A -> Prop) t x)). Qed.
Lemma lem3483557 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3483556 A t x) (@lem3483553 A t f s x h1 h2)). Qed.
Lemma lem3483560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3483562 {A : Type'} (t : A -> Prop) (x : A) : (term344 A t x) = (term369 A t x).
Proof. exact (@lem3483560 (@I (A -> Prop) t x)). Qed.
Lemma lem3483565 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term346 A f t x) : term369 A t x.
Proof. exact (EQ_MP (@lem3483562 A t x) (@lem3483370 A f t x h1)). Qed.
Lemma lem3483568 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : False.
Proof. exact (@lem3483565 A f t x h1 (@lem3483557 A t f s x h1 h2)). Qed.
Lemma lem3483569 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3483568 A t f s x h1 h2). Qed.
Lemma lem3483571 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483572 : term370 = False.
Proof. exact (@lem3483571 False). Qed.
Lemma lem3483573 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term346 A f t x) (h2 : term536 A t f s x) : False.
Proof. exact (EQ_MP (@lem3483572) (@lem3483569 A t f s x h1 h2)). Qed.
Lemma lem3483575 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem3483179 A f x') (@lem3483023 A f x' h1)). Qed.
Lemma lem3483576 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : term371 A f x'.
Proof. exact (fun h0 : term338 A f x' => @lem3483575 A f x' h1). Qed.
Lemma lem3483578 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483579 {A : Type'} (f : type686 A) (x' : A -> Prop) : (term371 A f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3483578 (@I ((A -> Prop) -> Prop) f x')). Qed.
Lemma lem3483580 {A : Type'} (f : type686 A) (x' : A -> Prop) (h1 : f x') : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem3483579 A f x') (@lem3483576 A f x' h1)). Qed.
Lemma lem3483586 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3483587 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : (term366 A f _36710 s x) = (term381 A s x f _36710).
Proof. exact (@lem3483586 (@I (A -> Prop) s x) (term338 A f _36710)). Qed.
Lemma lem3483593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483594 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : (term382 A f _36710 s x) = (term383 A s x f _36710).
Proof. exact (MK_COMB (@lem3483593) (@lem3483587 A s x f _36710)). Qed.
Lemma lem3483600 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : (term381 A s x f _36710) = (term381 A s x f _36710).
Proof. exact (eq_refl (term381 A s x f _36710)). Qed.
Lemma lem3483601 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : ((term366 A f _36710 s x) = (term381 A s x f _36710)) = ((term381 A s x f _36710) = (term381 A s x f _36710)).
Proof. exact (MK_COMB (@lem3483594 A s x f _36710) (@lem3483600 A s x f _36710)). Qed.
Lemma lem3483603 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3483604 (x : Prop) : (x = x) = True.
Proof. exact (@lem3483603 Prop x). Qed.
Lemma lem3483605 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : ((term381 A s x f _36710) = (term381 A s x f _36710)) = True.
Proof. exact (@lem3483604 (term381 A s x f _36710)). Qed.
Lemma lem3483606 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : ((term366 A f _36710 s x) = (term381 A s x f _36710)) = True.
Proof. exact (TRANS (@lem3483601 A s x f _36710) (@lem3483605 A s x f _36710)). Qed.
Lemma lem3483607 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : True = ((term366 A f _36710 s x) = (term381 A s x f _36710)).
Proof. exact (SYM (@lem3483606 A s x f _36710)). Qed.
Lemma lem3483608 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (_36710 : A -> Prop) : (term366 A f _36710 s x) = (term381 A s x f _36710).
Proof. exact (EQ_MP (@lem3483607 A s x f _36710) (@lem0)). Qed.
Lemma lem3483609 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term381 A s x f _36710.
Proof. exact (EQ_MP (@lem3483608 A s x f _36710) (@lem3483398 A _36710 t f s x h1)). Qed.
Lemma lem3483611 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3483612 {A : Type'} (f : type686 A) (_36710 : A -> Prop) (s : A -> Prop) (x : A) : (term381 A s x f _36710) = (term384 A f _36710 s x).
Proof. exact (@lem3483611 (term338 A f _36710) (@I (A -> Prop) s x)). Qed.
Lemma lem3483614 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3483615 {A : Type'} (f : type686 A) (_36710 : A -> Prop) : (term377 A f _36710) = (@I ((A -> Prop) -> Prop) f _36710).
Proof. exact (@lem3483614 (@I ((A -> Prop) -> Prop) f _36710)). Qed.
Lemma lem3483616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3483617 {A : Type'} (f : type686 A) (_36710 : A -> Prop) : (term378 A f _36710) = (term379 A f _36710).
Proof. exact (MK_COMB (@lem3483616) (@lem3483615 A f _36710)). Qed.
Lemma lem3483618 {A : Type'} (s : A -> Prop) (x : A) : (@I (A -> Prop) s x) = (@I (A -> Prop) s x).
Proof. exact (eq_refl (@I (A -> Prop) s x)). Qed.
Lemma lem3483619 {A : Type'} (f : type686 A) (_36710 : A -> Prop) (s : A -> Prop) (x : A) : (term384 A f _36710 s x) = (term385 A f _36710 s x).
Proof. exact (MK_COMB (@lem3483617 A f _36710) (@lem3483618 A s x)). Qed.
Lemma lem3483620 {A : Type'} (f : type686 A) (_36710 : A -> Prop) (s : A -> Prop) (x : A) : (term381 A s x f _36710) = (term385 A f _36710 s x).
Proof. exact (TRANS (@lem3483612 A f _36710 s x) (@lem3483619 A f _36710 s x)). Qed.
Lemma lem3483623 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term385 A f _36710 s x.
Proof. exact (EQ_MP (@lem3483620 A f _36710 s x) (@lem3483609 A _36710 t f s x h1)). Qed.
Lemma lem3483624 {A : Type'} (_36710 : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term385 A f _36710 s x.
Proof. exact (@lem3483623 A _36710 t f s x h1). Qed.
Lemma lem3483625 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term536 A t f s x) : term385 A f x' s x.
Proof. exact (@lem3483624 A x' t f s x h1). Qed.
Lemma lem3483628 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term536 A t f s x) : @I (A -> Prop) s x.
Proof. exact (@lem3483625 A x' t f s x h2 (@lem3483580 A f x' h1)). Qed.
Lemma lem3483629 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term536 A t f s x) : term367 A s x.
Proof. exact (fun h0 : term344 A s x => @lem3483628 A x' t f s x h1 h2). Qed.
Lemma lem3483631 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483632 {A : Type'} (s : A -> Prop) (x : A) : (term367 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3483631 (@I (A -> Prop) s x)). Qed.
Lemma lem3483633 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term536 A t f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3483632 A s x) (@lem3483629 A x' t f s x h1 h2)). Qed.
Lemma lem3483636 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3483638 {A : Type'} (s : A -> Prop) (x : A) : (term344 A s x) = (term369 A s x).
Proof. exact (@lem3483636 (@I (A -> Prop) s x)). Qed.
Lemma lem3483641 {A : Type'} (s : A -> Prop) (x : A) (h1 : term344 A s x) : term369 A s x.
Proof. exact (EQ_MP (@lem3483638 A s x) (@lem3483386 A s x h1)). Qed.
Lemma lem3483644 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : False.
Proof. exact (@lem3483641 A s x h1 (@lem3483633 A x' t f s x h2 h3)). Qed.
Lemma lem3483645 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : term370.
Proof. exact (fun h0 : ~ False => @lem3483644 A x' t f s x h1 h2 h3). Qed.
Lemma lem3483647 (p : Prop) : (term368 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3483648 : term370 = False.
Proof. exact (@lem3483647 False). Qed.
Lemma lem3483649 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : False.
Proof. exact (EQ_MP (@lem3483648) (@lem3483645 A x' t f s x h1 h2 h3)). Qed.
Lemma lem3483650 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3483649 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3483386 A s x h1)). Qed.
Lemma lem3483651 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : False.
Proof. exact (EQ_MP (@lem3483650 A x' t f s x h1 h2 h3) (@lem3483386 A s x h1)). Qed.
Lemma lem3483652 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3483497 A f t s x h1 h2) (fun h3 : False => @lem3483364 A s x h1)). Qed.
Lemma lem3483653 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483652 A f t s x h1 h2) (@lem3483364 A s x h1)). Qed.
Lemma lem3483654 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3483474 A f t s x h1 h2) (fun h3 : False => @lem3483350 A t x h1)). Qed.
Lemma lem3483655 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483654 A f t s x h1 h2) (@lem3483350 A t x h1)). Qed.
Lemma lem3483656 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3483651 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3483320 A s x h1)). Qed.
Lemma lem3483657 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : False.
Proof. exact (EQ_MP (@lem3483656 A x' t f s x h1 h2 h3) (@lem3483320 A s x h1)). Qed.
Lemma lem3483658 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3483653 A f t s x h1 h2) (fun h3 : False => @lem3483254 A s x h1)). Qed.
Lemma lem3483659 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483658 A f t s x h1 h2) (@lem3483254 A s x h1)). Qed.
Lemma lem3483660 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3483655 A f t s x h1 h2) (fun h3 : False => @lem3483225 A t x h1)). Qed.
Lemma lem3483661 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483660 A f t s x h1 h2) (@lem3483225 A t x h1)). Qed.
Lemma lem3483662 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h4 : term344 A s x => @lem3483657 A x' t f s x h1 h2 h3) (fun h4 : False => @lem3483320 A s x h1)). Qed.
Lemma lem3483663 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : f x') (h3 : term536 A t f s x) : False.
Proof. exact (EQ_MP (@lem3483662 A x' t f s x h1 h2 h3) (@lem3483320 A s x h1)). Qed.
Lemma lem3483664 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : (term344 A s x) = False.
Proof. exact (prop_ext (fun h3 : term344 A s x => @lem3483659 A f t s x h1 h2) (fun h3 : False => @lem3483254 A s x h1)). Qed.
Lemma lem3483665 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483664 A f t s x h1 h2) (@lem3483254 A s x h1)). Qed.
Lemma lem3483666 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : (term344 A t x) = False.
Proof. exact (prop_ext (fun h3 : term344 A t x => @lem3483661 A f t s x h1 h2) (fun h3 : False => @lem3483225 A t x h1)). Qed.
Lemma lem3483667 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A t x) (h2 : term541 A f t s x) : False.
Proof. exact (EQ_MP (@lem3483666 A f t s x h1 h2) (@lem3483225 A t x h1)). Qed.
Lemma lem3483668 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term536 A t f s x) : False.
Proof. exact (or_elim (@lem3483192 A t f s x h2) (fun h0 : term346 A f t x => @lem3483573 A t f s x h0 h2) (fun h0 : term344 A s x => @lem3483663 A x' t f s x h0 h1 h2)). Qed.
Lemma lem3483669 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term541 A f t s x) : False.
Proof. exact (or_elim (@lem3483185 A f t s x h1) (fun h0 : term344 A t x => @lem3483667 A f t s x h0 h1) (fun h0 : term344 A s x => @lem3483665 A f t s x h0 h1)). Qed.
Lemma lem3483670 {A : Type'} (x' : A -> Prop) (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : f x') (h2 : term526 A t f s x) : False.
Proof. exact (or_elim (@lem3483171 A t f s x h2) (fun h0 : term541 A f t s x => @lem3483669 A f t s x h0) (fun h0 : term536 A t f s x => @lem3483668 A x' t f s x h1 h0)). Qed.
Lemma lem3483671 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term526 A t f s x) : False.
Proof. exact (ex_elim (@lem3482676 A f h1) (fun x' : A -> Prop => fun h0 : term211 A f x' => @lem3483670 A x' t f s x h0 h2)). Qed.
Lemma lem3483672 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term432 A f s x) : False.
Proof. exact (ex_elim (@lem3483021 A f s x h2) (fun t : A -> Prop => fun h0 : term528 A f s x t => @lem3483671 A t f s x h1 h0)). Qed.
Lemma lem3483673 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term432 A f s x) : (term432 A f s x) = False.
Proof. exact (prop_ext (fun h3 : term432 A f s x => @lem3483672 A f s x h1 h2) (fun h3 : False => @lem3482654 A f s x h2)). Qed.
Lemma lem3483674 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term147 A f) (h2 : term432 A f s x) : False.
Proof. exact (EQ_MP (@lem3483673 A f s x h1 h2) (@lem3482654 A f s x h2)). Qed.
Lemma lem3483675 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term147 A f) : term431 A f s x.
Proof. exact (fun h0 : term432 A f s x => @lem3483674 A f s x h1 h0). Qed.
Lemma lem3483676 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term147 A f) : (term395 A f s x) = (term412 A f s x).
Proof. exact (EQ_MP (@lem3482653 A f s x) (@lem3483675 A s x f h1)). Qed.
Lemma lem3483681 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term147 A f) : term415 A f s.
Proof. exact (fun x : A => @lem3483676 A s x f h1). Qed.
Lemma lem3483682 {A : Type'} (f : type686 A) (s : A -> Prop) : term416 A f s.
Proof. exact (fun h0 : term147 A f => @lem3483681 A s f h0). Qed.
Lemma lem3483687 {A : Type'} (s : A -> Prop) : term426 A s.
Proof. exact (fun f : type686 A => @lem3483682 A f s). Qed.
Lemma lem3483692 {A : Type'} : term430 A.
Proof. exact (fun s : A -> Prop => @lem3483687 A s). Qed.
Lemma lem3483693 {A : Type'} : term429 A.
Proof. exact (EQ_MP (@lem3482648 A) (@lem3483692 A)). Qed.
Lemma lem3483694 {A : Type'} (s : A -> Prop) : term548 A s.
Proof. exact (@lem3483693 A s). Qed.
Lemma lem3483695 {A : Type'} (s : A -> Prop) : (term548 A s) = (term425 A s).
Proof. exact (eq_refl (term548 A s)). Qed.
Lemma lem3483696 {A : Type'} (s : A -> Prop) : term425 A s.
Proof. exact (EQ_MP (@lem3483695 A s) (@lem3483694 A s)). Qed.
Lemma lem3483697 {A : Type'} (s : A -> Prop) (f : type686 A) : term549 A s f.
Proof. exact (@lem3483696 A s f). Qed.
Lemma lem3483698 {A : Type'} (f : type686 A) (s : A -> Prop) : (term549 A s f) = (term417 A f s).
Proof. exact (eq_refl (term549 A s f)). Qed.
Lemma lem3483699 {A : Type'} (f : type686 A) (s : A -> Prop) : term417 A f s.
Proof. exact (EQ_MP (@lem3483698 A f s) (@lem3483697 A s f)). Qed.
Lemma lem3483701 {A : Type'} (f : type686 A) (s : A -> Prop) : term417 A f s.
Proof. exact (@lem3482492 A f s (@lem3483699 A f s)). Qed.
Lemma lem3483702 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term418 A f s) : False.
Proof. exact (@lem3483701 A f s (@lem3482476 A f s h1)). Qed.
Lemma lem3483703 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term418 A f s) : (term418 A f s) = False.
Proof. exact (prop_ext (fun h2 : term418 A f s => @lem3483702 A f s h1) (fun h2 : False => @lem3482476 A f s h1)). Qed.
Lemma lem3483704 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term418 A f s) : False.
Proof. exact (EQ_MP (@lem3483703 A f s h1) (@lem3482476 A f s h1)). Qed.
Lemma lem3483705 {A : Type'} (f : type686 A) (s : A -> Prop) : term417 A f s.
Proof. exact (fun h0 : term418 A f s => @lem3483704 A f s h0). Qed.
Lemma lem3483706 {A : Type'} (f : type686 A) (s : A -> Prop) : term416 A f s.
Proof. exact (EQ_MP (@lem3482475 A f s) (@lem3483705 A f s)). Qed.
Lemma lem3483707 {A : Type'} (f : type686 A) (s : A -> Prop) : term390 A f s.
Proof. exact (EQ_MP (@lem3482471 A f s) (@lem3483706 A f s)). Qed.
Lemma lem3483708 {A : Type'} (f : type686 A) (s : A -> Prop) : term389 A f s.
Proof. exact (EQ_MP (@lem3482304 A f s) (@lem3483707 A f s)). Qed.
Lemma lem3483709 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term31 A f s) = (term132 A f s).
Proof. exact (@lem3483708 A f s (@lem3480456 A f h1)). Qed.
Lemma lem3483712 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term31 A f s) = (term29 A f s).
Proof. exact (EQ_MP (@lem3480788 A f s) (@lem3483709 A s f h1)). Qed.
Lemma lem3483713 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term23 A f) = ((term31 A f s) = (term29 A f s)).
Proof. exact (prop_ext (fun h2 : term23 A f => @lem3483712 A s f h1) (fun h2 : (term31 A f s) = (term29 A f s) => @lem3480456 A f h1)). Qed.
Lemma lem3483714 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term31 A f s) = (term29 A f s).
Proof. exact (EQ_MP (@lem3483713 A s f h1) (@lem3480456 A f h1)). Qed.
Lemma lem3483715 {A : Type'} (f : type686 A) (s : A -> Prop) : term33 A f s.
Proof. exact (fun h0 : term23 A f => @lem3483714 A s f h0). Qed.
Lemma lem3483716 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term31 A f s) = s.
Proof. exact (EQ_MP (@lem3480686 A s f h1) (@lem0)). Qed.
Lemma lem3483717 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = ((term31 A f s) = s).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY (A -> Prop)) => @lem3483716 A s f h1) (fun h2 : (term31 A f s) = s => @lem3480439 A f h1)). Qed.
Lemma lem3483718 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term31 A f s) = s.
Proof. exact (EQ_MP (@lem3483717 A s f h1) (@lem3480439 A f h1)). Qed.
Lemma lem3483719 {A : Type'} (f : type686 A) (s : A -> Prop) : term36 A f s.
Proof. exact (fun h0 : f = (@EMPTY (A -> Prop)) => @lem3483718 A s f h0). Qed.
Lemma lem3483720 {A : Type'} (f : type686 A) (s : A -> Prop) : term39 A f s.
Proof. exact (conj (@lem3483719 A f s) (@lem3483715 A f s)). Qed.
Lemma lem3483721 {A : Type'} (f : type686 A) (s : A -> Prop) : (term31 A f s) = (term40 A f s).
Proof. exact (EQ_MP (@lem3480438 A f s) (@lem3483720 A f s)). Qed.
Lemma lem3483722 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term9 A s f) = (term7 A f s).
Proof. exact (EQ_MP (@lem3480629 A f s) (@lem3482246 A s f h1)). Qed.
Lemma lem3483723 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term23 A f) = ((term9 A s f) = (term7 A f s)).
Proof. exact (prop_ext (fun h2 : term23 A f => @lem3483722 A s f h1) (fun h2 : (term9 A s f) = (term7 A f s) => @lem3480404 A f h1)). Qed.
Lemma lem3483724 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) : (term9 A s f) = (term7 A f s).
Proof. exact (EQ_MP (@lem3483723 A s f h1) (@lem3480404 A f h1)). Qed.
Lemma lem3483725 {A : Type'} (f : type686 A) (s : A -> Prop) : term12 A f s.
Proof. exact (fun h0 : term23 A f => @lem3483724 A s f h0). Qed.
Lemma lem3483726 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term9 A s f) = s.
Proof. exact (EQ_MP (@lem3480527 A s f h1) (@lem0)). Qed.
Lemma lem3483727 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = ((term9 A s f) = s).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY (A -> Prop)) => @lem3483726 A s f h1) (fun h2 : (term9 A s f) = s => @lem3480387 A f h1)). Qed.
Lemma lem3483728 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term9 A s f) = s.
Proof. exact (EQ_MP (@lem3483727 A s f h1) (@lem3480387 A f h1)). Qed.
Lemma lem3483729 {A : Type'} (f : type686 A) (s : A -> Prop) : term16 A f s.
Proof. exact (fun h0 : f = (@EMPTY (A -> Prop)) => @lem3483728 A s f h0). Qed.
Lemma lem3483730 {A : Type'} (f : type686 A) (s : A -> Prop) : term19 A f s.
Proof. exact (conj (@lem3483729 A f s) (@lem3483725 A f s)). Qed.
Lemma lem3483731 {A : Type'} (f : type686 A) (s : A -> Prop) : (term9 A s f) = (term20 A f s).
Proof. exact (EQ_MP (@lem3480386 A f s) (@lem3483730 A f s)). Qed.
Lemma lem3483736 {A : Type'} (f : type686 A) : term550 A f.
Proof. exact (fun s : A -> Prop => @lem3483721 A f s). Qed.
Lemma lem3483741 {A : Type'} : term551 A.
Proof. exact (fun f : type686 A => @lem3483736 A f). Qed.
Lemma lem3483746 {A : Type'} (f : type686 A) : term552 A f.
Proof. exact (fun s : A -> Prop => @lem3483731 A f s). Qed.
Lemma lem3483751 {A : Type'} : term553 A.
Proof. exact (fun f : type686 A => @lem3483746 A f). Qed.
Lemma lem3483752 {A : Type'} : term554 A.
Proof. exact (conj (@lem3483751 A) (@lem3483741 A)). Qed.
