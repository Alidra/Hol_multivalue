Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_UNIONS_CHAIN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_SUBSET_UNIONS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import SUBSET_spec.
Require Import UNIONS_IN_CHAIN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3781457 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3781458 {A : Type'} (f : type686 A) (h1 : term0 A) : term1 A f.
Proof. exact (@lem3781457 A h1 f). Qed.
Lemma lem3781459 {A : Type'} (f : type686 A) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem3781460 {A : Type'} (f : type686 A) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem3781459 A f) (@lem3781458 A f h1)). Qed.
Lemma lem3781461 {A : Type'} (f : type686 A) (h1 : term3 A f) : term3 A f.
Proof. exact (h1). Qed.
Lemma lem3781462 {A : Type'} (f : type686 A) (h1 : term0 A) (h2 : term3 A f) : term4 A f.
Proof. exact (@lem3781460 A f h1 (@lem3781461 A f h2)). Qed.
Lemma lem3781463 {A : Type'} (f : type686 A) (h1 : term3 A f) : term5 A f.
Proof. exact (fun h0 : term0 A => @lem3781462 A f h0 h1). Qed.
Lemma lem3781464 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3781465 {A : Type'} (f : type686 A) (h1 : term0 A) (h2 : term3 A f) : term4 A f.
Proof. exact (@lem3781463 A f h2 (@lem3781464 A h1)). Qed.
Lemma lem3781466 {A : Type'} (f : type686 A) (h1 : term0 A) : term2 A f.
Proof. exact (fun h0 : term3 A f => @lem3781465 A f h1 h0). Qed.
Lemma lem3781467 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun f : type686 A => @lem3781466 A f h1). Qed.
Lemma lem3781468 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem3781467 A h0). Qed.
Lemma lem3781469 {A : Type'} : term0 A.
Proof. exact (@lem3781468 A (@lem3768988 A)). Qed.
Lemma lem3781470 {A : Type'} (f : type686 A) : term1 A f.
Proof. exact (@lem3781469 A f). Qed.
Lemma lem3781471 {A : Type'} (f : type686 A) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem3781473 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem3781474 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3781475 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3781474 A s) (@lem3781473 A s)). Qed.
Lemma lem3781476 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem3781475 A s t). Qed.
Lemma lem3781477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem3781479 {A : Type'} (t : type686 A) : term11 A t.
Proof. exact (@lem9784 (t = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3781480 {A : Type'} (t : type686 A) : (term11 A t) = (term12 A t).
Proof. exact (eq_refl (term11 A t)). Qed.
Lemma lem3781481 {A : Type'} (t : type686 A) : term12 A t.
Proof. exact (EQ_MP (@lem3781480 A t) (@lem3781479 A t)). Qed.
Lemma lem3781482 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : t = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3781483 {A : Type'} (t : type686 A) (h1 : term13 A t) : term13 A t.
Proof. exact (h1). Qed.
Lemma lem3781484 {A : Type'} : term14 A.
Proof. exact (@lem3756509 A). Qed.
Lemma lem3781485 {A : Type'} (f : type686 A) : term15 A f.
Proof. exact (@lem3781484 A f). Qed.
Lemma lem3781486 {A : Type'} (f : type686 A) : (term15 A f) = (term16 A f).
Proof. exact (eq_refl (term15 A f)). Qed.
Lemma lem3781487 {A : Type'} (f : type686 A) : term16 A f.
Proof. exact (EQ_MP (@lem3781486 A f) (@lem3781485 A f)). Qed.
Lemma lem3781488 {A : Type'} (f : type686 A) (s : A -> Prop) : term17 A f s.
Proof. exact (@lem3781487 A f s). Qed.
Lemma lem3781489 {A : Type'} (f : type686 A) (s : A -> Prop) : (term17 A f s) = (term18 A f s).
Proof. exact (eq_refl (term17 A f s)). Qed.
Lemma lem3781490 {A : Type'} (f : type686 A) (s : A -> Prop) : term18 A f s.
Proof. exact (EQ_MP (@lem3781489 A f s) (@lem3781488 A f s)). Qed.
Lemma lem3781491 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term19 A s f) : term19 A s f.
Proof. exact (h1). Qed.
Lemma lem3781492 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term20 A s f) : term20 A s f.
Proof. exact (h1). Qed.
Lemma lem3781493 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3781494 {A : Type'} (f : type686 A) (h1 : term21 A f) : term21 A f.
Proof. exact (h1). Qed.
Lemma lem3781495 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem3781496 {A : Type'} (f : type686 A) (h1 : term23 A f) : term23 A f.
Proof. exact (h1). Qed.
Lemma lem3781497 {A : Type'} (f : type686 A) (h1 : term13 A f) : term13 A f.
Proof. exact (h1). Qed.
Lemma lem3781498 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3781499 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem3781500 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem3781499 A P) (@lem3781498 A P)). Qed.
Lemma lem3781501 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem3781500 A P Q). Qed.
Lemma lem3781502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem3781504 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3781506 {A : Type'} (s : A -> Prop) (f : type686 A) : (term22 A s f) = ((term22 A s f) = True).
Proof. exact (@lem7 (term22 A s f)). Qed.
Lemma lem3781536 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3781504 A s) (@lem3781493 A s h1)). Qed.
Lemma lem3781537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781538 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term29 A s) = (and True).
Proof. exact (MK_COMB (@lem3781537) (@lem3781536 A s h1)). Qed.
Lemma lem3781540 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : (term22 A s f) = True.
Proof. exact (EQ_MP (@lem3781506 A s f) (@lem3781495 A s f h1)). Qed.
Lemma lem3781541 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term30 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem3781538 A s h1) (@lem3781540 A s f h2)). Qed.
Lemma lem3781543 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3781544 : (True /\ True) = True.
Proof. exact (@lem3781543 True). Qed.
Lemma lem3781545 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term30 A s f) = True.
Proof. exact (TRANS (@lem3781541 A s f h1 h2) (@lem3781544)). Qed.
Lemma lem3781546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781547 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term31 A s f) = (imp True).
Proof. exact (MK_COMB (@lem3781546) (@lem3781545 A s f h1 h2)). Qed.
Lemma lem3781556 {A : Type'} (f : type686 A) (s : A -> Prop) : (term32 A f s) = (term32 A f s).
Proof. exact (eq_refl (term32 A f s)). Qed.
Lemma lem3781557 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term18 A f s) = (term33 A f s).
Proof. exact (MK_COMB (@lem3781547 A s f h1 h2) (@lem3781556 A f s)). Qed.
Lemma lem3781559 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3781560 {A : Type'} (f : type686 A) (s : A -> Prop) : (term33 A f s) = (term32 A f s).
Proof. exact (@lem3781559 (term32 A f s)). Qed.
Lemma lem3781569 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term18 A f s) = (term32 A f s).
Proof. exact (TRANS (@lem3781557 A s f h1 h2) (@lem3781560 A f s)). Qed.
Lemma lem3781570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781571 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term34 A f s) = (term35 A f s).
Proof. exact (MK_COMB (@lem3781570) (@lem3781569 A s f h1 h2)). Qed.
Lemma lem3781578 {A : Type'} (f : type686 A) (s : A -> Prop) : (term36 A f s) = (term36 A f s).
Proof. exact (eq_refl (term36 A f s)). Qed.
Lemma lem3781579 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term37 A f s) = (term38 A f s).
Proof. exact (MK_COMB (@lem3781571 A s f h1 h2) (@lem3781578 A f s)). Qed.
Lemma lem3781581 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem3781502 A P Q) (@lem3781501 A P Q)). Qed.
Lemma lem3781582 {A : Type'} (P : type180 A) (Q : Prop) : (term39 A P Q) = (term40 A P Q).
Proof. exact (@lem3781581 (type686 A) P Q). Qed.
Lemma lem3781583 {A : Type'} (f : type686 A) (s : A -> Prop) : (term41 A f s) = (term42 A f s).
Proof. exact (@lem3781582 A (term43 A f s) (term36 A f s)). Qed.
Lemma lem3781584 {A : Type'} (f : type686 A) (s : A -> Prop) (f' : type686 A) : (term44 A f s f') = (term45 A f s f').
Proof. exact (eq_refl (term44 A f s f')). Qed.
Lemma lem3781585 {A : Type'} (f : type686 A) (s : A -> Prop) : (term46 A f s) = (term43 A f s).
Proof. exact (fun_ext (fun f' : type686 A => @lem3781584 A f s f')). Qed.
Lemma lem3781586 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem3781587 {A : Type'} (f : type686 A) (s : A -> Prop) : (term47 A f s) = (term32 A f s).
Proof. exact (MK_COMB (@lem3781586 A) (@lem3781585 A f s)). Qed.
Lemma lem3781588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781589 {A : Type'} (f : type686 A) (s : A -> Prop) : (term48 A f s) = (term35 A f s).
Proof. exact (MK_COMB (@lem3781588) (@lem3781587 A f s)). Qed.
Lemma lem3781590 {A : Type'} (f : type686 A) (s : A -> Prop) : (term36 A f s) = (term36 A f s).
Proof. exact (eq_refl (term36 A f s)). Qed.
Lemma lem3781591 {A : Type'} (f : type686 A) (s : A -> Prop) : (term41 A f s) = (term38 A f s).
Proof. exact (MK_COMB (@lem3781589 A f s) (@lem3781590 A f s)). Qed.
Lemma lem3781592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3781593 {A : Type'} (f : type686 A) (s : A -> Prop) : (term49 A f s) = (term50 A f s).
Proof. exact (MK_COMB (@lem3781592) (@lem3781591 A f s)). Qed.
Lemma lem3781594 {A : Type'} (f : type686 A) (s : A -> Prop) (f' : type686 A) : (term44 A f s f') = (term45 A f s f').
Proof. exact (eq_refl (term44 A f s f')). Qed.
Lemma lem3781595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781596 {A : Type'} (f : type686 A) (s : A -> Prop) (f' : type686 A) : (term51 A f s f') = (term52 A f s f').
Proof. exact (MK_COMB (@lem3781595) (@lem3781594 A f s f')). Qed.
Lemma lem3781597 {A : Type'} (f : type686 A) (s : A -> Prop) : (term36 A f s) = (term36 A f s).
Proof. exact (eq_refl (term36 A f s)). Qed.
Lemma lem3781598 {A : Type'} (f' : type686 A) (f : type686 A) (s : A -> Prop) : (term53 A f' f s) = (term54 A f' f s).
Proof. exact (MK_COMB (@lem3781596 A f s f') (@lem3781597 A f s)). Qed.
Lemma lem3781599 {A : Type'} (f : type686 A) (s : A -> Prop) : (term55 A f s) = (term56 A f s).
Proof. exact (fun_ext (fun f' : type686 A => @lem3781598 A f' f s)). Qed.
Lemma lem3781600 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3781601 {A : Type'} (f : type686 A) (s : A -> Prop) : (term42 A f s) = (term57 A f s).
Proof. exact (MK_COMB (@lem3781600 A) (@lem3781599 A f s)). Qed.
Lemma lem3781602 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term41 A f s) = (term42 A f s)) = ((term38 A f s) = (term57 A f s)).
Proof. exact (MK_COMB (@lem3781593 A f s) (@lem3781601 A f s)). Qed.
Lemma lem3781603 {A : Type'} (f : type686 A) (s : A -> Prop) : (term38 A f s) = (term57 A f s).
Proof. exact (EQ_MP (@lem3781602 A f s) (@lem3781583 A f s)). Qed.
Lemma lem3781620 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term37 A f s) = (term57 A f s).
Proof. exact (TRANS (@lem3781579 A s f h1 h2) (@lem3781603 A f s)). Qed.
Lemma lem3781621 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term57 A f s) = (term37 A f s).
Proof. exact (SYM (@lem3781620 A s f h1 h2)). Qed.
Lemma lem3781657 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term58 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3781658 (p : Prop) (q : Prop) (p' : Prop) : term59 p q p'.
Proof. exact (fun q' : Prop => @lem3781657 p q p' q'). Qed.
Lemma lem3781659 (p : Prop) (q : Prop) : term60 p q.
Proof. exact (fun p' : Prop => @lem3781658 p q p'). Qed.
Lemma lem3781660 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term61 A t f s.
Proof. exact (@lem3781659 (term45 A f s t) (term36 A f s)). Qed.
Lemma lem3781661 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) : term62 A t f s p'.
Proof. exact (@lem3781660 A t f s p'). Qed.
Lemma lem3781662 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) : (term62 A t f s p') = (term63 A t f s p').
Proof. exact (eq_refl (term62 A t f s p')). Qed.
Lemma lem3781663 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) : term63 A t f s p'.
Proof. exact (EQ_MP (@lem3781662 A t f s p') (@lem3781661 A t f s p')). Qed.
Lemma lem3781664 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term64 A t f s p' q'.
Proof. exact (@lem3781663 A t f s p' q'). Qed.
Lemma lem3781665 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term64 A t f s p' q') = (term65 A t f s p' q').
Proof. exact (eq_refl (term64 A t f s p' q')). Qed.
Lemma lem3781666 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term65 A t f s p' q'.
Proof. exact (EQ_MP (@lem3781665 A t f s p' q') (@lem3781664 A t f s p' q')). Qed.
Lemma lem3781670 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : t = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3781671 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem3781672 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (@FINITE (A -> Prop) t) = (@FINITE (A -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3781671 A) (@lem3781670 A t h1)). Qed.
Lemma lem3781673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781674 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term66 A t) = (term67 A).
Proof. exact (MK_COMB (@lem3781673) (@lem3781672 A t h1)). Qed.
Lemma lem3781678 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : t = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3781679 {A : Type'} : (@SUBSET (A -> Prop)) = (@SUBSET (A -> Prop)).
Proof. exact (eq_refl (@SUBSET (A -> Prop))). Qed.
Lemma lem3781680 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (@SUBSET (A -> Prop) t) = (@SUBSET (A -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3781679 A) (@lem3781678 A t h1)). Qed.
Lemma lem3781681 {A : Type'} (f : type686 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3781682 {A : Type'} (f : type686 A) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (@SUBSET (A -> Prop) t f) = (@SUBSET (A -> Prop) (@EMPTY (A -> Prop)) f).
Proof. exact (MK_COMB (@lem3781680 A t h1) (@lem3781681 A f)). Qed.
Lemma lem3781683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781684 {A : Type'} (f : type686 A) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term68 A t f) = (term69 A f).
Proof. exact (MK_COMB (@lem3781683) (@lem3781682 A f t h1)). Qed.
Lemma lem3781686 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : t = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3781687 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3781688 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (@UNIONS A t) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3781687 A) (@lem3781686 A t h1)). Qed.
Lemma lem3781690 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem3781691 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem3781690 A). Qed.
Lemma lem3781692 {A : Type'} (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (@UNIONS A t) = (@EMPTY A).
Proof. exact (TRANS (@lem3781688 A t h1) (@lem3781691 A)). Qed.
Lemma lem3781693 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@SUBSET A s).
Proof. exact (eq_refl (@SUBSET A s)). Qed.
Lemma lem3781694 {A : Type'} (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term22 A s t) = (@SUBSET A s (@EMPTY A)).
Proof. exact (MK_COMB (@lem3781693 A s) (@lem3781692 A t h1)). Qed.
Lemma lem3781695 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term70 A f s t) = (term71 A f s).
Proof. exact (MK_COMB (@lem3781684 A f t h1) (@lem3781694 A s t h1)). Qed.
Lemma lem3781698 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term45 A f s t) = (term72 A f s).
Proof. exact (MK_COMB (@lem3781674 A t h1) (@lem3781695 A f s t h1)). Qed.
Lemma lem3781703 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (q' : Prop) : term73 A t f s q'.
Proof. exact (@lem3781666 A t f s (term72 A f s) q'). Qed.
Lemma lem3781704 {A : Type'} (f : type686 A) (s : A -> Prop) (q' : Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : term74 A t f s q'.
Proof. exact (@lem3781703 A t f s q' (@lem3781698 A f s t h1)). Qed.
Lemma lem3781726 {A : Type'} (f : type686 A) (s : A -> Prop) : (term36 A f s) = (term36 A f s).
Proof. exact (eq_refl (term36 A f s)). Qed.
Lemma lem3781727 {A : Type'} (f : type686 A) (s : A -> Prop) : term75 A f s.
Proof. exact (fun h0 : term72 A f s => @lem3781726 A f s). Qed.
Lemma lem3781728 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : term76 A t f s.
Proof. exact (@lem3781704 A f s (term36 A f s) t h1). Qed.
Lemma lem3781729 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term54 A t f s) = (term77 A f s).
Proof. exact (@lem3781728 A f s t h1 (@lem3781727 A f s)). Qed.
Lemma lem3781789 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : t = (@EMPTY (A -> Prop))) : (term77 A f s) = (term54 A t f s).
Proof. exact (SYM (@lem3781729 A f s t h1)). Qed.
Lemma lem3781800 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : term78 A f s.
Proof. exact (conj (@lem3781495 A s f h2) (@lem3781493 A s h1)). Qed.
Lemma lem3781801 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term13 A f) (h3 : term22 A s f) : term79 A f s.
Proof. exact (conj (@lem3781497 A f h2) (@lem3781800 A s f h1 h3)). Qed.
Lemma lem3781802 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term80 A f s.
Proof. exact (conj (@lem3781496 A f h1) (@lem3781801 A s f h2 h3 h4)). Qed.
Lemma lem3781803 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : t = (@EMPTY (A -> Prop))) (h5 : term22 A s f) : term81 A t f s.
Proof. exact (conj (@lem3781482 A t h4) (@lem3781802 A s f h1 h2 h3 h5)). Qed.
Lemma lem3781811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3781812 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term83 A s t).
Proof. exact (@lem3781811 (A -> Prop) s t). Qed.
Lemma lem3781813 {A : Type'} (t : type686 A) : (t = (@EMPTY (A -> Prop))) = (term84 A t).
Proof. exact (@lem3781812 A t (@EMPTY (A -> Prop))). Qed.
Lemma lem3781822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781823 {A : Type'} (t : type686 A) : (term85 A t) = (term86 A t).
Proof. exact (MK_COMB (@lem3781822) (@lem3781813 A t)). Qed.
Lemma lem3781841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781842 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3781841 A s t). Qed.
Lemma lem3781843 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term10 A t u).
Proof. exact (@lem3781842 A t u). Qed.
Lemma lem3781850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3781851 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term87 A t u) = (term88 A t u).
Proof. exact (MK_COMB (@lem3781850) (@lem3781843 A t u)). Qed.
Lemma lem3781853 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781854 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3781853 A s t). Qed.
Lemma lem3781855 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (@SUBSET A u t) = (term10 A u t).
Proof. exact (@lem3781854 A u t). Qed.
Lemma lem3781862 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term89 A u t) = (term90 A u t).
Proof. exact (MK_COMB (@lem3781851 A t u) (@lem3781855 A u t)). Qed.
Lemma lem3781865 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) : (term91 A t u f) = (term91 A t u f).
Proof. exact (eq_refl (term91 A t u f)). Qed.
Lemma lem3781866 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term92 A f u t) = (term93 A f u t).
Proof. exact (MK_COMB (@lem3781865 A t u f) (@lem3781862 A u t)). Qed.
Lemma lem3781869 {A : Type'} (f : type686 A) (t : A -> Prop) : (term94 A f t) = (term95 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3781866 A f u t)). Qed.
Lemma lem3781870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3781871 {A : Type'} (f : type686 A) (t : A -> Prop) : (term96 A f t) = (term97 A f t).
Proof. exact (MK_COMB (@lem3781870 A) (@lem3781869 A f t)). Qed.
Lemma lem3781876 {A : Type'} (f : type686 A) : (term98 A f) = (term99 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3781871 A f t)). Qed.
Lemma lem3781877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3781878 {A : Type'} (f : type686 A) : (term23 A f) = (term100 A f).
Proof. exact (MK_COMB (@lem3781877 A) (@lem3781876 A f)). Qed.
Lemma lem3781883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781884 {A : Type'} (f : type686 A) : (term101 A f) = (term102 A f).
Proof. exact (MK_COMB (@lem3781883) (@lem3781878 A f)). Qed.
Lemma lem3781890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3781891 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term83 A s t).
Proof. exact (@lem3781890 (A -> Prop) s t). Qed.
Lemma lem3781892 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term84 A f).
Proof. exact (@lem3781891 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3781901 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3781902 {A : Type'} (f : type686 A) : (term13 A f) = (term103 A f).
Proof. exact (MK_COMB (@lem3781901) (@lem3781892 A f)). Qed.
Lemma lem3781903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781904 {A : Type'} (f : type686 A) : (term104 A f) = (term105 A f).
Proof. exact (MK_COMB (@lem3781903) (@lem3781902 A f)). Qed.
Lemma lem3781908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3781908 A s t). Qed.
Lemma lem3781910 {A : Type'} (s : A -> Prop) (f : type686 A) : (term22 A s f) = (term106 A s f).
Proof. exact (@lem3781909 A s (@UNIONS A f)). Qed.
Lemma lem3781917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781918 {A : Type'} (s : A -> Prop) (f : type686 A) : (term107 A s f) = (term108 A s f).
Proof. exact (MK_COMB (@lem3781917) (@lem3781910 A s f)). Qed.
Lemma lem3781919 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3781920 {A : Type'} (f : type686 A) (s : A -> Prop) : (term78 A f s) = (term109 A f s).
Proof. exact (MK_COMB (@lem3781918 A s f) (@lem3781919 A s)). Qed.
Lemma lem3781923 {A : Type'} (f : type686 A) (s : A -> Prop) : (term79 A f s) = (term110 A f s).
Proof. exact (MK_COMB (@lem3781904 A f) (@lem3781920 A f s)). Qed.
Lemma lem3781926 {A : Type'} (f : type686 A) (s : A -> Prop) : (term80 A f s) = (term111 A f s).
Proof. exact (MK_COMB (@lem3781884 A f) (@lem3781923 A f s)). Qed.
Lemma lem3781929 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term81 A t f s) = (term112 A t f s).
Proof. exact (MK_COMB (@lem3781823 A t) (@lem3781926 A f s)). Qed.
Lemma lem3781932 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781933 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term113 A t f s) = (term114 A t f s).
Proof. exact (MK_COMB (@lem3781932) (@lem3781929 A t f s)). Qed.
Lemma lem3781941 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781942 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem3781941 (A -> Prop) s t). Qed.
Lemma lem3781943 {A : Type'} (f : type686 A) : (@SUBSET (A -> Prop) (@EMPTY (A -> Prop)) f) = (term116 A f).
Proof. exact (@lem3781942 A (@EMPTY (A -> Prop)) f). Qed.
Lemma lem3781950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3781951 {A : Type'} (f : type686 A) : (term69 A f) = (term117 A f).
Proof. exact (MK_COMB (@lem3781950) (@lem3781943 A f)). Qed.
Lemma lem3781953 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3781953 A s t). Qed.
Lemma lem3781955 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (term118 A s).
Proof. exact (@lem3781954 A s (@EMPTY A)). Qed.
Lemma lem3781962 {A : Type'} (f : type686 A) (s : A -> Prop) : (term71 A f s) = (term119 A f s).
Proof. exact (MK_COMB (@lem3781951 A f) (@lem3781955 A s)). Qed.
Lemma lem3781965 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem3781966 {A : Type'} (f : type686 A) (s : A -> Prop) : (term72 A f s) = (term120 A f s).
Proof. exact (MK_COMB (@lem3781965 A) (@lem3781962 A f s)). Qed.
Lemma lem3781969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3781970 {A : Type'} (f : type686 A) (s : A -> Prop) : (term121 A f s) = (term122 A f s).
Proof. exact (MK_COMB (@lem3781969) (@lem3781966 A f s)). Qed.
Lemma lem3781978 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3781979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3781978 A s t). Qed.
Lemma lem3781986 {A : Type'} (t : A -> Prop) (f : type686 A) : (term123 A t f) = (term123 A t f).
Proof. exact (eq_refl (term123 A t f)). Qed.
Lemma lem3781987 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term124 A f s t) = (term125 A f s t).
Proof. exact (MK_COMB (@lem3781986 A t f) (@lem3781979 A s t)). Qed.
Lemma lem3781990 {A : Type'} (f : type686 A) (s : A -> Prop) : (term126 A f s) = (term127 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3781987 A f s t)). Qed.
Lemma lem3781991 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3781992 {A : Type'} (f : type686 A) (s : A -> Prop) : (term36 A f s) = (term128 A f s).
Proof. exact (MK_COMB (@lem3781991 A) (@lem3781990 A f s)). Qed.
Lemma lem3781997 {A : Type'} (f : type686 A) (s : A -> Prop) : (term77 A f s) = (term129 A f s).
Proof. exact (MK_COMB (@lem3781970 A f s) (@lem3781992 A f s)). Qed.
Lemma lem3782000 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term130 A t f s) = (term131 A t f s).
Proof. exact (MK_COMB (@lem3781933 A t f s) (@lem3781997 A f s)). Qed.
Lemma lem3782003 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term131 A t f s) = (term130 A t f s).
Proof. exact (SYM (@lem3782000 A t f s)). Qed.
Lemma lem3782015 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782016 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782015 (A -> Prop) P x). Qed.
Lemma lem3782017 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem3782016 A t x). Qed.
Lemma lem3782018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3782019 {A : Type'} (t : type686 A) (x : A -> Prop) : (term132 A x t) = (term133 A t x).
Proof. exact (MK_COMB (@lem3782018) (@lem3782017 A t x)). Qed.
Lemma lem3782021 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3782022 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3782021 (A -> Prop) x). Qed.
Lemma lem3782023 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem3782019 A t x) (@lem3782022 A x)). Qed.
Lemma lem3782025 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3782026 {A : Type'} (t : type686 A) (x : A -> Prop) : ((t x) = False) = (term134 A t x).
Proof. exact (@lem3782025 (t x)). Qed.
Lemma lem3782027 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term134 A t x).
Proof. exact (TRANS (@lem3782023 A t x) (@lem3782026 A t x)). Qed.
Lemma lem3782028 {A : Type'} (t : type686 A) : (term135 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782027 A t x)). Qed.
Lemma lem3782029 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782030 {A : Type'} (t : type686 A) : (term84 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3782029 A) (@lem3782028 A t)). Qed.
Lemma lem3782035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782036 {A : Type'} (t : type686 A) : (term86 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3782035) (@lem3782030 A t)). Qed.
Lemma lem3782052 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782053 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782052 (A -> Prop) P x). Qed.
Lemma lem3782054 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3782053 A f t). Qed.
Lemma lem3782055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782056 {A : Type'} (f : type686 A) (t : A -> Prop) : (term123 A t f) = (term139 A f t).
Proof. exact (MK_COMB (@lem3782055) (@lem3782054 A f t)). Qed.
Lemma lem3782058 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782059 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782058 (A -> Prop) P x). Qed.
Lemma lem3782060 {A : Type'} (f : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u f) = (f u).
Proof. exact (@lem3782059 A f u). Qed.
Lemma lem3782061 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term140 A t u f) = (term141 A t f u).
Proof. exact (MK_COMB (@lem3782056 A f t) (@lem3782060 A f u)). Qed.
Lemma lem3782064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782065 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term91 A t u f) = (term142 A t f u).
Proof. exact (MK_COMB (@lem3782064) (@lem3782061 A t f u)). Qed.
Lemma lem3782075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782076 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782075 A P x). Qed.
Lemma lem3782077 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3782076 A t x). Qed.
Lemma lem3782078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782079 {A : Type'} (t : A -> Prop) (x : A) : (term143 A x t) = (term144 A t x).
Proof. exact (MK_COMB (@lem3782078) (@lem3782077 A t x)). Qed.
Lemma lem3782081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782082 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782081 A P x). Qed.
Lemma lem3782083 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3782082 A u x). Qed.
Lemma lem3782084 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term145 A t x u) = (term146 A t u x).
Proof. exact (MK_COMB (@lem3782079 A t x) (@lem3782083 A u x)). Qed.
Lemma lem3782087 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term147 A t u) = (term148 A t u).
Proof. exact (fun_ext (fun x : A => @lem3782084 A t u x)). Qed.
Lemma lem3782088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782089 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term10 A t u) = (term149 A t u).
Proof. exact (MK_COMB (@lem3782088 A) (@lem3782087 A t u)). Qed.
Lemma lem3782094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3782095 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term88 A t u) = (term150 A t u).
Proof. exact (MK_COMB (@lem3782094) (@lem3782089 A t u)). Qed.
Lemma lem3782103 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782104 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782103 A P x). Qed.
Lemma lem3782105 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3782104 A u x). Qed.
Lemma lem3782106 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782107 {A : Type'} (u : A -> Prop) (x : A) : (term143 A x u) = (term144 A u x).
Proof. exact (MK_COMB (@lem3782106) (@lem3782105 A u x)). Qed.
Lemma lem3782109 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782110 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782109 A P x). Qed.
Lemma lem3782111 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3782110 A t x). Qed.
Lemma lem3782112 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term145 A u x t) = (term146 A u t x).
Proof. exact (MK_COMB (@lem3782107 A u x) (@lem3782111 A t x)). Qed.
Lemma lem3782115 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term147 A u t) = (term148 A u t).
Proof. exact (fun_ext (fun x : A => @lem3782112 A u t x)). Qed.
Lemma lem3782116 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782117 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term10 A u t) = (term149 A u t).
Proof. exact (MK_COMB (@lem3782116 A) (@lem3782115 A u t)). Qed.
Lemma lem3782122 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term90 A u t) = (term151 A u t).
Proof. exact (MK_COMB (@lem3782095 A t u) (@lem3782117 A u t)). Qed.
Lemma lem3782125 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term93 A f u t) = (term152 A f u t).
Proof. exact (MK_COMB (@lem3782065 A t f u) (@lem3782122 A u t)). Qed.
Lemma lem3782128 {A : Type'} (f : type686 A) (t : A -> Prop) : (term95 A f t) = (term153 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3782125 A f u t)). Qed.
Lemma lem3782129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782130 {A : Type'} (f : type686 A) (t : A -> Prop) : (term97 A f t) = (term154 A f t).
Proof. exact (MK_COMB (@lem3782129 A) (@lem3782128 A f t)). Qed.
Lemma lem3782135 {A : Type'} (f : type686 A) : (term99 A f) = (term155 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782130 A f t)). Qed.
Lemma lem3782136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782137 {A : Type'} (f : type686 A) : (term100 A f) = (term156 A f).
Proof. exact (MK_COMB (@lem3782136 A) (@lem3782135 A f)). Qed.
Lemma lem3782142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782143 {A : Type'} (f : type686 A) : (term102 A f) = (term157 A f).
Proof. exact (MK_COMB (@lem3782142) (@lem3782137 A f)). Qed.
Lemma lem3782153 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782154 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782153 (A -> Prop) P x). Qed.
Lemma lem3782155 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3782154 A f x). Qed.
Lemma lem3782156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3782157 {A : Type'} (f : type686 A) (x : A -> Prop) : (term132 A x f) = (term133 A f x).
Proof. exact (MK_COMB (@lem3782156) (@lem3782155 A f x)). Qed.
Lemma lem3782159 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3782160 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3782159 (A -> Prop) x). Qed.
Lemma lem3782161 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3782157 A f x) (@lem3782160 A x)). Qed.
Lemma lem3782163 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3782164 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term134 A f x).
Proof. exact (@lem3782163 (f x)). Qed.
Lemma lem3782165 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term134 A f x).
Proof. exact (TRANS (@lem3782161 A f x) (@lem3782164 A f x)). Qed.
Lemma lem3782166 {A : Type'} (f : type686 A) : (term135 A f) = (term136 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782165 A f x)). Qed.
Lemma lem3782167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782168 {A : Type'} (f : type686 A) : (term84 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3782167 A) (@lem3782166 A f)). Qed.
Lemma lem3782173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3782174 {A : Type'} (f : type686 A) : (term103 A f) = (term158 A f).
Proof. exact (MK_COMB (@lem3782173) (@lem3782168 A f)). Qed.
Lemma lem3782175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782176 {A : Type'} (f : type686 A) : (term105 A f) = (term159 A f).
Proof. exact (MK_COMB (@lem3782175) (@lem3782174 A f)). Qed.
Lemma lem3782186 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782187 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782186 A P x). Qed.
Lemma lem3782188 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3782187 A s x). Qed.
Lemma lem3782189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782190 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3782189) (@lem3782188 A s x)). Qed.
Lemma lem3782192 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3782193 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (@lem3782192 A s x). Qed.
Lemma lem3782194 {A : Type'} (f : type686 A) (x : A) : (term160 A x f) = (term161 A f x).
Proof. exact (@lem3782193 A f x). Qed.
Lemma lem3782202 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782203 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782202 (A -> Prop) P x). Qed.
Lemma lem3782204 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3782203 A f t). Qed.
Lemma lem3782205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782206 {A : Type'} (f : type686 A) (t : A -> Prop) : (term123 A t f) = (term139 A f t).
Proof. exact (MK_COMB (@lem3782205) (@lem3782204 A f t)). Qed.
Lemma lem3782208 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782209 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782208 A P x). Qed.
Lemma lem3782210 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3782209 A t x). Qed.
Lemma lem3782211 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term162 A f x t) = (term163 A f t x).
Proof. exact (MK_COMB (@lem3782206 A f t) (@lem3782210 A t x)). Qed.
Lemma lem3782214 {A : Type'} (f : type686 A) (x : A) : (term164 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782211 A f t x)). Qed.
Lemma lem3782215 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782216 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3782215 A) (@lem3782214 A f x)). Qed.
Lemma lem3782221 {A : Type'} (f : type686 A) (x : A) : (term160 A x f) = (term166 A f x).
Proof. exact (TRANS (@lem3782194 A f x) (@lem3782216 A f x)). Qed.
Lemma lem3782222 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term167 A s x f) = (term168 A s f x).
Proof. exact (MK_COMB (@lem3782190 A s x) (@lem3782221 A f x)). Qed.
Lemma lem3782225 {A : Type'} (s : A -> Prop) (f : type686 A) : (term169 A s f) = (term170 A s f).
Proof. exact (fun_ext (fun x : A => @lem3782222 A s f x)). Qed.
Lemma lem3782226 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782227 {A : Type'} (s : A -> Prop) (f : type686 A) : (term106 A s f) = (term171 A s f).
Proof. exact (MK_COMB (@lem3782226 A) (@lem3782225 A s f)). Qed.
Lemma lem3782232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782233 {A : Type'} (s : A -> Prop) (f : type686 A) : (term108 A s f) = (term172 A s f).
Proof. exact (MK_COMB (@lem3782232) (@lem3782227 A s f)). Qed.
Lemma lem3782234 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3782235 {A : Type'} (f : type686 A) (s : A -> Prop) : (term109 A f s) = (term173 A f s).
Proof. exact (MK_COMB (@lem3782233 A s f) (@lem3782234 A s)). Qed.
Lemma lem3782238 {A : Type'} (f : type686 A) (s : A -> Prop) : (term110 A f s) = (term174 A f s).
Proof. exact (MK_COMB (@lem3782176 A f) (@lem3782235 A f s)). Qed.
Lemma lem3782241 {A : Type'} (f : type686 A) (s : A -> Prop) : (term111 A f s) = (term175 A f s).
Proof. exact (MK_COMB (@lem3782143 A f) (@lem3782238 A f s)). Qed.
Lemma lem3782244 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term112 A t f s) = (term176 A t f s).
Proof. exact (MK_COMB (@lem3782036 A t) (@lem3782241 A f s)). Qed.
Lemma lem3782247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782248 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term114 A t f s) = (term177 A t f s).
Proof. exact (MK_COMB (@lem3782247) (@lem3782244 A t f s)). Qed.
Lemma lem3782262 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3782263 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3782262 (A -> Prop) x). Qed.
Lemma lem3782264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782265 {A : Type'} (x : A -> Prop) : (term178 A x) = (imp False).
Proof. exact (MK_COMB (@lem3782264) (@lem3782263 A x)). Qed.
Lemma lem3782267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782268 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782267 (A -> Prop) P x). Qed.
Lemma lem3782269 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3782268 A f x). Qed.
Lemma lem3782270 {A : Type'} (f : type686 A) (x : A -> Prop) : (term179 A x f) = (term180 A f x).
Proof. exact (MK_COMB (@lem3782265 A x) (@lem3782269 A f x)). Qed.
Lemma lem3782272 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3782273 {A : Type'} (f : type686 A) (x : A -> Prop) : (term180 A f x) = True.
Proof. exact (@lem3782272 (f x)). Qed.
Lemma lem3782274 {A : Type'} (x : A -> Prop) (f : type686 A) : (term179 A x f) = True.
Proof. exact (TRANS (@lem3782270 A f x) (@lem3782273 A f x)). Qed.
Lemma lem3782275 {A : Type'} (f : type686 A) : (term181 A f) = (term182 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782274 A x f)). Qed.
Lemma lem3782276 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782277 {A : Type'} (f : type686 A) : (term116 A f) = (term183 A).
Proof. exact (MK_COMB (@lem3782276 A) (@lem3782275 A f)). Qed.
Lemma lem3782279 {A : Type'} (t : Prop) : (term184 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3782280 {A : Type'} (t : Prop) : (term185 A t) = t.
Proof. exact (@lem3782279 (A -> Prop) t). Qed.
Lemma lem3782281 {A : Type'} : (term183 A) = True.
Proof. exact (@lem3782280 A True). Qed.
Lemma lem3782282 {A : Type'} (f : type686 A) : (term116 A f) = True.
Proof. exact (TRANS (@lem3782277 A f) (@lem3782281 A)). Qed.
Lemma lem3782283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782284 {A : Type'} (f : type686 A) : (term117 A f) = (and True).
Proof. exact (MK_COMB (@lem3782283) (@lem3782282 A f)). Qed.
Lemma lem3782292 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782293 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782292 A P x). Qed.
Lemma lem3782294 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3782293 A s x). Qed.
Lemma lem3782295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782296 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3782295) (@lem3782294 A s x)). Qed.
Lemma lem3782298 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3782299 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3782298 A x). Qed.
Lemma lem3782300 {A : Type'} (s : A -> Prop) (x : A) : (term186 A s x) = (term187 A s x).
Proof. exact (MK_COMB (@lem3782296 A s x) (@lem3782299 A x)). Qed.
Lemma lem3782302 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3782303 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term188 A s x).
Proof. exact (@lem3782302 (s x)). Qed.
Lemma lem3782304 {A : Type'} (s : A -> Prop) (x : A) : (term186 A s x) = (term188 A s x).
Proof. exact (TRANS (@lem3782300 A s x) (@lem3782303 A s x)). Qed.
Lemma lem3782305 {A : Type'} (s : A -> Prop) : (term189 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem3782304 A s x)). Qed.
Lemma lem3782306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782307 {A : Type'} (s : A -> Prop) : (term118 A s) = (term191 A s).
Proof. exact (MK_COMB (@lem3782306 A) (@lem3782305 A s)). Qed.
Lemma lem3782312 {A : Type'} (f : type686 A) (s : A -> Prop) : (term119 A f s) = (term192 A s).
Proof. exact (MK_COMB (@lem3782284 A f) (@lem3782307 A s)). Qed.
Lemma lem3782314 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3782315 {A : Type'} (s : A -> Prop) : (term192 A s) = (term191 A s).
Proof. exact (@lem3782314 (term191 A s)). Qed.
Lemma lem3782320 {A : Type'} (f : type686 A) (s : A -> Prop) : (term119 A f s) = (term191 A s).
Proof. exact (TRANS (@lem3782312 A f s) (@lem3782315 A s)). Qed.
Lemma lem3782321 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem3782322 {A : Type'} (f : type686 A) (s : A -> Prop) : (term120 A f s) = (term193 A s).
Proof. exact (MK_COMB (@lem3782321 A) (@lem3782320 A f s)). Qed.
Lemma lem3782325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782326 {A : Type'} (f : type686 A) (s : A -> Prop) : (term122 A f s) = (term194 A s).
Proof. exact (MK_COMB (@lem3782325) (@lem3782322 A f s)). Qed.
Lemma lem3782334 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782335 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3782334 (A -> Prop) P x). Qed.
Lemma lem3782336 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3782335 A f t). Qed.
Lemma lem3782337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782338 {A : Type'} (f : type686 A) (t : A -> Prop) : (term123 A t f) = (term139 A f t).
Proof. exact (MK_COMB (@lem3782337) (@lem3782336 A f t)). Qed.
Lemma lem3782346 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782347 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782346 A P x). Qed.
Lemma lem3782348 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3782347 A s x). Qed.
Lemma lem3782349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782350 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3782349) (@lem3782348 A s x)). Qed.
Lemma lem3782352 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3782353 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3782352 A P x). Qed.
Lemma lem3782354 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3782353 A t x). Qed.
Lemma lem3782355 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term145 A s x t) = (term146 A s t x).
Proof. exact (MK_COMB (@lem3782350 A s x) (@lem3782354 A t x)). Qed.
Lemma lem3782358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term148 A s t).
Proof. exact (fun_ext (fun x : A => @lem3782355 A s t x)). Qed.
Lemma lem3782359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3782359 A) (@lem3782358 A s t)). Qed.
Lemma lem3782365 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term125 A f s t) = (term195 A f s t).
Proof. exact (MK_COMB (@lem3782338 A f t) (@lem3782360 A s t)). Qed.
Lemma lem3782368 {A : Type'} (f : type686 A) (s : A -> Prop) : (term127 A f s) = (term196 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782365 A f s t)). Qed.
Lemma lem3782369 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782370 {A : Type'} (f : type686 A) (s : A -> Prop) : (term128 A f s) = (term197 A f s).
Proof. exact (MK_COMB (@lem3782369 A) (@lem3782368 A f s)). Qed.
Lemma lem3782375 {A : Type'} (f : type686 A) (s : A -> Prop) : (term129 A f s) = (term198 A f s).
Proof. exact (MK_COMB (@lem3782326 A f s) (@lem3782370 A f s)). Qed.
Lemma lem3782378 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term131 A t f s) = (term199 A t f s).
Proof. exact (MK_COMB (@lem3782248 A t f s) (@lem3782375 A f s)). Qed.
Lemma lem3782381 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term199 A t f s) = (term131 A t f s).
Proof. exact (SYM (@lem3782378 A t f s)). Qed.
Lemma lem3782383 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3782384 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term199 A t f s) = (term201 A t f s).
Proof. exact (@lem3782383 (term199 A t f s)). Qed.
Lemma lem3782385 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term201 A t f s) = (term199 A t f s).
Proof. exact (SYM (@lem3782384 A t f s)). Qed.
Lemma lem3782386 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term202 A t f s) : term202 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782389 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term201 A t f s) : term201 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782390 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term203 A t f s.
Proof. exact (fun h0 : term201 A t f s => @lem3782389 A t f s h0). Qed.
Lemma lem3782391 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term203 A t f s) : term203 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782392 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term201 A t f s) : term201 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782393 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term201 A t f s) (h2 : term203 A t f s) : term201 A t f s.
Proof. exact (@lem3782391 A t f s h2 (@lem3782392 A t f s h1)). Qed.
Lemma lem3782394 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term201 A t f s) : term204 A t f s.
Proof. exact (fun h0 : term203 A t f s => @lem3782393 A t f s h1 h0). Qed.
Lemma lem3782395 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term203 A t f s) : term203 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782396 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term201 A t f s) (h2 : term203 A t f s) : term201 A t f s.
Proof. exact (@lem3782394 A t f s h1 (@lem3782395 A t f s h2)). Qed.
Lemma lem3782397 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term203 A t f s) : term203 A t f s.
Proof. exact (fun h0 : term201 A t f s => @lem3782396 A t f s h0 h1). Qed.
Lemma lem3782398 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term205 A t f s.
Proof. exact (fun h0 : term203 A t f s => @lem3782397 A t f s h0). Qed.
Lemma lem3782401 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term203 A t f s.
Proof. exact (@lem3782398 A t f s (@lem3782390 A t f s)). Qed.
Lemma lem3782402 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term203 A t f s.
Proof. exact (@lem3782401 A t f s). Qed.
Lemma lem3782416 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3782417 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term201 A t f s) = (term206 A t f s).
Proof. exact (@lem3782416 (term202 A t f s)). Qed.
Lemma lem3782419 (t : Prop) : (term207 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3782420 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term206 A t f s) = (term199 A t f s).
Proof. exact (@lem3782419 (term199 A t f s)). Qed.
Lemma lem3782423 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term201 A t f s) = (term199 A t f s).
Proof. exact (TRANS (@lem3782417 A t f s) (@lem3782420 A t f s)). Qed.
Lemma lem3782546 {A : Type'} (f : type686 A) (s : A -> Prop) : (term208 A f s) = (term209 A f s).
Proof. exact (fun_ext (fun t : type686 A => @lem3782423 A t f s)). Qed.
Lemma lem3782547 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3782548 {A : Type'} (f : type686 A) (s : A -> Prop) : (term210 A f s) = (term211 A f s).
Proof. exact (MK_COMB (@lem3782547 A) (@lem3782546 A f s)). Qed.
Lemma lem3782553 {A : Type'} (s : A -> Prop) : (term212 A s) = (term213 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3782548 A f s)). Qed.
Lemma lem3782554 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3782555 {A : Type'} (s : A -> Prop) : (term214 A s) = (term215 A s).
Proof. exact (MK_COMB (@lem3782554 A) (@lem3782553 A s)). Qed.
Lemma lem3782560 {A : Type'} : (term216 A) = (term217 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3782555 A s)). Qed.
Lemma lem3782561 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782570 {A : Type'} : (term218 A) = (term219 A).
Proof. exact (MK_COMB (@lem3782561 A) (@lem3782560 A)). Qed.
Lemma lem3782575 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A s t x) = (term146 A s t x).
Proof. exact (eq_refl (term146 A s t x)). Qed.
Lemma lem3782576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term148 A s t) = (term148 A s t).
Proof. exact (fun_ext (fun x : A => @lem3782575 A s t x)). Qed.
Lemma lem3782577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782578 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3782577 A) (@lem3782576 A s t)). Qed.
Lemma lem3782581 {A : Type'} (f : type686 A) (t : A -> Prop) : (term139 A f t) = (term139 A f t).
Proof. exact (eq_refl (term139 A f t)). Qed.
Lemma lem3782582 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term195 A f s t) = (term195 A f s t).
Proof. exact (MK_COMB (@lem3782581 A f t) (@lem3782578 A s t)). Qed.
Lemma lem3782583 {A : Type'} (f : type686 A) (s : A -> Prop) : (term196 A f s) = (term196 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782582 A f s t)). Qed.
Lemma lem3782584 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782585 {A : Type'} (f : type686 A) (s : A -> Prop) : (term197 A f s) = (term197 A f s).
Proof. exact (MK_COMB (@lem3782584 A) (@lem3782583 A f s)). Qed.
Lemma lem3782588 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term188 A s x).
Proof. exact (eq_refl (term188 A s x)). Qed.
Lemma lem3782589 {A : Type'} (s : A -> Prop) : (term190 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem3782588 A s x)). Qed.
Lemma lem3782590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782591 {A : Type'} (s : A -> Prop) : (term191 A s) = (term191 A s).
Proof. exact (MK_COMB (@lem3782590 A) (@lem3782589 A s)). Qed.
Lemma lem3782594 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem3782595 {A : Type'} (s : A -> Prop) : (term193 A s) = (term193 A s).
Proof. exact (MK_COMB (@lem3782594 A) (@lem3782591 A s)). Qed.
Lemma lem3782596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782597 {A : Type'} (s : A -> Prop) : (term194 A s) = (term194 A s).
Proof. exact (MK_COMB (@lem3782596) (@lem3782595 A s)). Qed.
Lemma lem3782598 {A : Type'} (f : type686 A) (s : A -> Prop) : (term198 A f s) = (term198 A f s).
Proof. exact (MK_COMB (@lem3782597 A s) (@lem3782585 A f s)). Qed.
Lemma lem3782599 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3782604 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term163 A f t x) = (term163 A f t x).
Proof. exact (eq_refl (term163 A f t x)). Qed.
Lemma lem3782605 {A : Type'} (f : type686 A) (x : A) : (term165 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782604 A f t x)). Qed.
Lemma lem3782606 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782607 {A : Type'} (f : type686 A) (x : A) : (term166 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3782606 A) (@lem3782605 A f x)). Qed.
Lemma lem3782610 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term144 A s x).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem3782611 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term168 A s f x).
Proof. exact (MK_COMB (@lem3782610 A s x) (@lem3782607 A f x)). Qed.
Lemma lem3782612 {A : Type'} (s : A -> Prop) (f : type686 A) : (term170 A s f) = (term170 A s f).
Proof. exact (fun_ext (fun x : A => @lem3782611 A s f x)). Qed.
Lemma lem3782613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782614 {A : Type'} (s : A -> Prop) (f : type686 A) : (term171 A s f) = (term171 A s f).
Proof. exact (MK_COMB (@lem3782613 A) (@lem3782612 A s f)). Qed.
Lemma lem3782615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782616 {A : Type'} (s : A -> Prop) (f : type686 A) : (term172 A s f) = (term172 A s f).
Proof. exact (MK_COMB (@lem3782615) (@lem3782614 A s f)). Qed.
Lemma lem3782617 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term173 A f s).
Proof. exact (MK_COMB (@lem3782616 A s f) (@lem3782599 A s)). Qed.
Lemma lem3782620 {A : Type'} (f : type686 A) (x : A -> Prop) : (term134 A f x) = (term134 A f x).
Proof. exact (eq_refl (term134 A f x)). Qed.
Lemma lem3782621 {A : Type'} (f : type686 A) : (term136 A f) = (term136 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782620 A f x)). Qed.
Lemma lem3782622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782623 {A : Type'} (f : type686 A) : (term137 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3782622 A) (@lem3782621 A f)). Qed.
Lemma lem3782624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3782625 {A : Type'} (f : type686 A) : (term158 A f) = (term158 A f).
Proof. exact (MK_COMB (@lem3782624) (@lem3782623 A f)). Qed.
Lemma lem3782626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782627 {A : Type'} (f : type686 A) : (term159 A f) = (term159 A f).
Proof. exact (MK_COMB (@lem3782626) (@lem3782625 A f)). Qed.
Lemma lem3782628 {A : Type'} (f : type686 A) (s : A -> Prop) : (term174 A f s) = (term174 A f s).
Proof. exact (MK_COMB (@lem3782627 A f) (@lem3782617 A f s)). Qed.
Lemma lem3782633 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term146 A u t x) = (term146 A u t x).
Proof. exact (eq_refl (term146 A u t x)). Qed.
Lemma lem3782634 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term148 A u t) = (term148 A u t).
Proof. exact (fun_ext (fun x : A => @lem3782633 A u t x)). Qed.
Lemma lem3782635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782636 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term149 A u t) = (term149 A u t).
Proof. exact (MK_COMB (@lem3782635 A) (@lem3782634 A u t)). Qed.
Lemma lem3782641 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term146 A t u x) = (term146 A t u x).
Proof. exact (eq_refl (term146 A t u x)). Qed.
Lemma lem3782642 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term148 A t u) = (term148 A t u).
Proof. exact (fun_ext (fun x : A => @lem3782641 A t u x)). Qed.
Lemma lem3782643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782644 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term149 A t u) = (term149 A t u).
Proof. exact (MK_COMB (@lem3782643 A) (@lem3782642 A t u)). Qed.
Lemma lem3782645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3782646 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term150 A t u) = (term150 A t u).
Proof. exact (MK_COMB (@lem3782645) (@lem3782644 A t u)). Qed.
Lemma lem3782647 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term151 A u t) = (term151 A u t).
Proof. exact (MK_COMB (@lem3782646 A t u) (@lem3782636 A u t)). Qed.
Lemma lem3782654 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term142 A t f u) = (term142 A t f u).
Proof. exact (eq_refl (term142 A t f u)). Qed.
Lemma lem3782655 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term152 A f u t).
Proof. exact (MK_COMB (@lem3782654 A t f u) (@lem3782647 A u t)). Qed.
Lemma lem3782656 {A : Type'} (f : type686 A) (t : A -> Prop) : (term153 A f t) = (term153 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3782655 A f u t)). Qed.
Lemma lem3782657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782658 {A : Type'} (f : type686 A) (t : A -> Prop) : (term154 A f t) = (term154 A f t).
Proof. exact (MK_COMB (@lem3782657 A) (@lem3782656 A f t)). Qed.
Lemma lem3782659 {A : Type'} (f : type686 A) : (term155 A f) = (term155 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782658 A f t)). Qed.
Lemma lem3782660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782661 {A : Type'} (f : type686 A) : (term156 A f) = (term156 A f).
Proof. exact (MK_COMB (@lem3782660 A) (@lem3782659 A f)). Qed.
Lemma lem3782662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782663 {A : Type'} (f : type686 A) : (term157 A f) = (term157 A f).
Proof. exact (MK_COMB (@lem3782662) (@lem3782661 A f)). Qed.
Lemma lem3782664 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term175 A f s).
Proof. exact (MK_COMB (@lem3782663 A f) (@lem3782628 A f s)). Qed.
Lemma lem3782667 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term134 A t x).
Proof. exact (eq_refl (term134 A t x)). Qed.
Lemma lem3782668 {A : Type'} (t : type686 A) : (term136 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782667 A t x)). Qed.
Lemma lem3782669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782670 {A : Type'} (t : type686 A) : (term137 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3782669 A) (@lem3782668 A t)). Qed.
Lemma lem3782671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782672 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3782671) (@lem3782670 A t)). Qed.
Lemma lem3782673 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term176 A t f s) = (term176 A t f s).
Proof. exact (MK_COMB (@lem3782672 A t) (@lem3782664 A f s)). Qed.
Lemma lem3782674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3782675 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term177 A t f s) = (term177 A t f s).
Proof. exact (MK_COMB (@lem3782674) (@lem3782673 A t f s)). Qed.
Lemma lem3782676 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term199 A t f s) = (term199 A t f s).
Proof. exact (MK_COMB (@lem3782675 A t f s) (@lem3782598 A f s)). Qed.
Lemma lem3782677 {A : Type'} (f : type686 A) (s : A -> Prop) : (term209 A f s) = (term209 A f s).
Proof. exact (fun_ext (fun t : type686 A => @lem3782676 A t f s)). Qed.
Lemma lem3782678 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3782679 {A : Type'} (f : type686 A) (s : A -> Prop) : (term211 A f s) = (term211 A f s).
Proof. exact (MK_COMB (@lem3782678 A) (@lem3782677 A f s)). Qed.
Lemma lem3782680 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3782679 A f s)). Qed.
Lemma lem3782681 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3782682 {A : Type'} (s : A -> Prop) : (term215 A s) = (term215 A s).
Proof. exact (MK_COMB (@lem3782681 A) (@lem3782680 A s)). Qed.
Lemma lem3782683 {A : Type'} : (term217 A) = (term217 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3782682 A s)). Qed.
Lemma lem3782684 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782685 {A : Type'} : (term219 A) = (term219 A).
Proof. exact (MK_COMB (@lem3782684 A) (@lem3782683 A)). Qed.
Lemma lem3782804 {A : Type'} : (term218 A) = (term219 A).
Proof. exact (TRANS (@lem3782570 A) (@lem3782685 A)). Qed.
Lemma lem3782805 {A : Type'} : (term219 A) = (term218 A).
Proof. exact (SYM (@lem3782804 A)). Qed.
Lemma lem3782806 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term176 A t f s) : term176 A t f s.
Proof. exact (h1). Qed.
Lemma lem3782807 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term193 A s.
Proof. exact (h1). Qed.
Lemma lem3782809 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3782810 {A : Type'} (f : type686 A) (s : A -> Prop) : (term197 A f s) = (term220 A f s).
Proof. exact (@lem3782809 (term197 A f s)). Qed.
Lemma lem3782811 {A : Type'} (f : type686 A) (s : A -> Prop) : (term220 A f s) = (term197 A f s).
Proof. exact (SYM (@lem3782810 A f s)). Qed.
Lemma lem3782812 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) : term221 A f s.
Proof. exact (h1). Qed.
Lemma lem3782813 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term134 A t x).
Proof. exact (eq_refl (term134 A t x)). Qed.
Lemma lem3782814 {A : Type'} (t : type686 A) : (term136 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782813 A t x)). Qed.
Lemma lem3782815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782816 {A : Type'} (t : type686 A) : (term137 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3782815 A) (@lem3782814 A t)). Qed.
Lemma lem3782823 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term222 A t f u) = (term223 A t f u).
Proof. exact (@lem17045 (f t) (f u)). Qed.
Lemma lem3782830 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term146 A t u x) = (term224 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3782831 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term148 A t u) = (term225 A t u).
Proof. exact (fun_ext (fun x : A => @lem3782830 A t u x)). Qed.
Lemma lem3782832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782833 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term149 A t u) = (term226 A t u).
Proof. exact (MK_COMB (@lem3782832 A) (@lem3782831 A t u)). Qed.
Lemma lem3782840 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term146 A u t x) = (term224 A u t x).
Proof. exact (@lem17265 (u x) (t x)). Qed.
Lemma lem3782841 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term148 A u t) = (term225 A u t).
Proof. exact (fun_ext (fun x : A => @lem3782840 A u t x)). Qed.
Lemma lem3782842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782843 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term149 A u t) = (term226 A u t).
Proof. exact (MK_COMB (@lem3782842 A) (@lem3782841 A u t)). Qed.
Lemma lem3782844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3782845 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term150 A t u) = (term227 A t u).
Proof. exact (MK_COMB (@lem3782844) (@lem3782833 A t u)). Qed.
Lemma lem3782846 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term151 A u t) = (term228 A u t).
Proof. exact (MK_COMB (@lem3782845 A t u) (@lem3782843 A u t)). Qed.
Lemma lem3782847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3782848 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term229 A t f u) = (term230 A t f u).
Proof. exact (MK_COMB (@lem3782847) (@lem3782823 A t f u)). Qed.
Lemma lem3782849 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term231 A f u t) = (term232 A f u t).
Proof. exact (MK_COMB (@lem3782848 A t f u) (@lem3782846 A u t)). Qed.
Lemma lem3782850 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term231 A f u t).
Proof. exact (@lem17265 (term141 A t f u) (term151 A u t)). Qed.
Lemma lem3782851 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term232 A f u t).
Proof. exact (TRANS (@lem3782850 A f u t) (@lem3782849 A f u t)). Qed.
Lemma lem3782852 {A : Type'} (f : type686 A) (t : A -> Prop) : (term153 A f t) = (term233 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3782851 A f u t)). Qed.
Lemma lem3782853 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782854 {A : Type'} (f : type686 A) (t : A -> Prop) : (term154 A f t) = (term234 A f t).
Proof. exact (MK_COMB (@lem3782853 A) (@lem3782852 A f t)). Qed.
Lemma lem3782855 {A : Type'} (f : type686 A) : (term155 A f) = (term235 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782854 A f t)). Qed.
Lemma lem3782856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3782857 {A : Type'} (f : type686 A) : (term156 A f) = (term236 A f).
Proof. exact (MK_COMB (@lem3782856 A) (@lem3782855 A f)). Qed.
Lemma lem3782860 {A : Type'} (f : type686 A) (x : A -> Prop) : (term237 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3782861 {A : Type'} (P : type686 A) : (term238 A P) = (term239 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3782862 {A : Type'} (f : type686 A) : (term158 A f) = (term240 A f).
Proof. exact (@lem3782861 A (term136 A f)). Qed.
Lemma lem3782863 {A : Type'} (f : type686 A) (x : A -> Prop) : (term241 A f x) = (term134 A f x).
Proof. exact (eq_refl (term241 A f x)). Qed.
Lemma lem3782864 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3782865 {A : Type'} (f : type686 A) (x : A -> Prop) : (term242 A f x) = (term237 A f x).
Proof. exact (MK_COMB (@lem3782864) (@lem3782863 A f x)). Qed.
Lemma lem3782866 {A : Type'} (f : type686 A) (x : A -> Prop) : (term242 A f x) = (f x).
Proof. exact (TRANS (@lem3782865 A f x) (@lem3782860 A f x)). Qed.
Lemma lem3782867 {A : Type'} (f : type686 A) : (term243 A f) = (term244 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3782866 A f x)). Qed.
Lemma lem3782868 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782869 {A : Type'} (f : type686 A) : (term240 A f) = (term245 A f).
Proof. exact (MK_COMB (@lem3782868 A) (@lem3782867 A f)). Qed.
Lemma lem3782870 {A : Type'} (f : type686 A) : (term158 A f) = (term245 A f).
Proof. exact (TRANS (@lem3782862 A f) (@lem3782869 A f)). Qed.
Lemma lem3782876 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term163 A f t x) = (term163 A f t x).
Proof. exact (eq_refl (term163 A f t x)). Qed.
Lemma lem3782877 {A : Type'} (f : type686 A) (x : A) : (term165 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3782876 A f t x)). Qed.
Lemma lem3782878 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3782879 {A : Type'} (f : type686 A) (x : A) : (term166 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3782878 A) (@lem3782877 A f x)). Qed.
Lemma lem3782881 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3782882 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term247 A s f x) = (term247 A s f x).
Proof. exact (MK_COMB (@lem3782881 A s x) (@lem3782879 A f x)). Qed.
Lemma lem3782883 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term247 A s f x).
Proof. exact (@lem17265 (s x) (term166 A f x)). Qed.
Lemma lem3782884 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term247 A s f x).
Proof. exact (TRANS (@lem3782883 A s f x) (@lem3782882 A s f x)). Qed.
Lemma lem3782885 {A : Type'} (s : A -> Prop) (f : type686 A) : (term170 A s f) = (term248 A s f).
Proof. exact (fun_ext (fun x : A => @lem3782884 A s f x)). Qed.
Lemma lem3782886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3782887 {A : Type'} (s : A -> Prop) (f : type686 A) : (term171 A s f) = (term249 A s f).
Proof. exact (MK_COMB (@lem3782886 A) (@lem3782885 A s f)). Qed.
Lemma lem3782888 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3782889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782890 {A : Type'} (s : A -> Prop) (f : type686 A) : (term172 A s f) = (term250 A s f).
Proof. exact (MK_COMB (@lem3782889) (@lem3782887 A s f)). Qed.
Lemma lem3782891 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term251 A f s).
Proof. exact (MK_COMB (@lem3782890 A s f) (@lem3782888 A s)). Qed.
Lemma lem3782892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782893 {A : Type'} (f : type686 A) : (term159 A f) = (term252 A f).
Proof. exact (MK_COMB (@lem3782892) (@lem3782870 A f)). Qed.
Lemma lem3782894 {A : Type'} (f : type686 A) (s : A -> Prop) : (term174 A f s) = (term253 A f s).
Proof. exact (MK_COMB (@lem3782893 A f) (@lem3782891 A f s)). Qed.
Lemma lem3782895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782896 {A : Type'} (f : type686 A) : (term157 A f) = (term254 A f).
Proof. exact (MK_COMB (@lem3782895) (@lem3782857 A f)). Qed.
Lemma lem3782897 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term255 A f s).
Proof. exact (MK_COMB (@lem3782896 A f) (@lem3782894 A f s)). Qed.
Lemma lem3782898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3782899 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3782898) (@lem3782816 A t)). Qed.
Lemma lem3782900 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term176 A t f s) = (term256 A t f s).
Proof. exact (MK_COMB (@lem3782899 A t) (@lem3782897 A f s)). Qed.
Lemma lem3783103 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3783104 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3783103 (A -> Prop) P Q). Qed.
Lemma lem3783105 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term261 A s f x) = (term262 A s f x).
Proof. exact (@lem3783104 A (term188 A s x) (term165 A f x)). Qed.
Lemma lem3783106 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term263 A f x t) = (term163 A f t x).
Proof. exact (eq_refl (term263 A f x t)). Qed.
Lemma lem3783107 {A : Type'} (f : type686 A) (x : A) : (term264 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783106 A f t x)). Qed.
Lemma lem3783108 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783109 {A : Type'} (f : type686 A) (x : A) : (term265 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3783108 A) (@lem3783107 A f x)). Qed.
Lemma lem3783110 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3783111 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term261 A s f x) = (term247 A s f x).
Proof. exact (MK_COMB (@lem3783110 A s x) (@lem3783109 A f x)). Qed.
Lemma lem3783112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783113 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term266 A s f x) = (term267 A s f x).
Proof. exact (MK_COMB (@lem3783112) (@lem3783111 A s f x)). Qed.
Lemma lem3783114 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term263 A f x t) = (term163 A f t x).
Proof. exact (eq_refl (term263 A f x t)). Qed.
Lemma lem3783115 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3783116 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term268 A s f x t) = (term269 A s f t x).
Proof. exact (MK_COMB (@lem3783115 A s x) (@lem3783114 A f t x)). Qed.
Lemma lem3783117 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term270 A s f x) = (term271 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783116 A s f t x)). Qed.
Lemma lem3783118 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783119 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term262 A s f x) = (term272 A s f x).
Proof. exact (MK_COMB (@lem3783118 A) (@lem3783117 A s f x)). Qed.
Lemma lem3783120 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term261 A s f x) = (term262 A s f x)) = ((term247 A s f x) = (term272 A s f x)).
Proof. exact (MK_COMB (@lem3783113 A s f x) (@lem3783119 A s f x)). Qed.
Lemma lem3783121 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term247 A s f x) = (term272 A s f x).
Proof. exact (EQ_MP (@lem3783120 A s f x) (@lem3783105 A s f x)). Qed.
Lemma lem3783122 {A : Type'} (s : A -> Prop) (f : type686 A) : (term248 A s f) = (term273 A s f).
Proof. exact (fun_ext (fun x : A => @lem3783121 A s f x)). Qed.
Lemma lem3783123 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783124 {A : Type'} (s : A -> Prop) (f : type686 A) : (term249 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem3783123 A) (@lem3783122 A s f)). Qed.
Lemma lem3783126 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3783127 {A : Type'} (P : type1364 A) : (term277 A P) = (term278 A P).
Proof. exact (@lem3783126 A (A -> Prop) P). Qed.
Lemma lem3783128 {A : Type'} (s : A -> Prop) (f : type686 A) : (term279 A s f) = (term280 A s f).
Proof. exact (@lem3783127 A (term281 A s f)). Qed.
Lemma lem3783129 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term282 A s f x) = (term271 A s f x).
Proof. exact (eq_refl (term282 A s f x)). Qed.
Lemma lem3783130 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3783131 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term283 A s f x t) = (term284 A s f x t).
Proof. exact (MK_COMB (@lem3783129 A s f x) (@lem3783130 A t)). Qed.
Lemma lem3783132 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term284 A s f x t) = (term269 A s f t x).
Proof. exact (eq_refl (term284 A s f x t)). Qed.
Lemma lem3783133 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term283 A s f x t) = (term269 A s f t x).
Proof. exact (TRANS (@lem3783131 A s f x t) (@lem3783132 A s f t x)). Qed.
Lemma lem3783134 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term285 A s f x) = (term271 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783133 A s f t x)). Qed.
Lemma lem3783135 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783136 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term286 A s f x) = (term272 A s f x).
Proof. exact (MK_COMB (@lem3783135 A) (@lem3783134 A s f x)). Qed.
Lemma lem3783137 {A : Type'} (s : A -> Prop) (f : type686 A) : (term287 A s f) = (term273 A s f).
Proof. exact (fun_ext (fun x : A => @lem3783136 A s f x)). Qed.
Lemma lem3783138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783139 {A : Type'} (s : A -> Prop) (f : type686 A) : (term279 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem3783138 A) (@lem3783137 A s f)). Qed.
Lemma lem3783140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783141 {A : Type'} (s : A -> Prop) (f : type686 A) : (term288 A s f) = (term289 A s f).
Proof. exact (MK_COMB (@lem3783140) (@lem3783139 A s f)). Qed.
Lemma lem3783142 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term282 A s f x) = (term271 A s f x).
Proof. exact (eq_refl (term282 A s f x)). Qed.
Lemma lem3783143 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3783144 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term290 A s f t x) = (term291 A s f t x).
Proof. exact (MK_COMB (@lem3783142 A s f x) (@lem3783143 A t x)). Qed.
Lemma lem3783145 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term291 A s f t x) = (term292 A s f t x).
Proof. exact (eq_refl (term291 A s f t x)). Qed.
Lemma lem3783146 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term290 A s f t x) = (term292 A s f t x).
Proof. exact (TRANS (@lem3783144 A s f t x) (@lem3783145 A s f t x)). Qed.
Lemma lem3783147 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term293 A s f t) = (term294 A s f t).
Proof. exact (fun_ext (fun x : A => @lem3783146 A s f t x)). Qed.
Lemma lem3783148 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783149 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term295 A s f t) = (term296 A s f t).
Proof. exact (MK_COMB (@lem3783148 A) (@lem3783147 A s f t)). Qed.
Lemma lem3783150 {A : Type'} (s : A -> Prop) (f : type686 A) : (term297 A s f) = (term298 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783149 A s f t)). Qed.
Lemma lem3783151 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783152 {A : Type'} (s : A -> Prop) (f : type686 A) : (term280 A s f) = (term299 A s f).
Proof. exact (MK_COMB (@lem3783151 A) (@lem3783150 A s f)). Qed.
Lemma lem3783153 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term279 A s f) = (term280 A s f)) = ((term274 A s f) = (term299 A s f)).
Proof. exact (MK_COMB (@lem3783141 A s f) (@lem3783152 A s f)). Qed.
Lemma lem3783154 {A : Type'} (s : A -> Prop) (f : type686 A) : (term274 A s f) = (term299 A s f).
Proof. exact (EQ_MP (@lem3783153 A s f) (@lem3783128 A s f)). Qed.
Lemma lem3783155 {A : Type'} (s : A -> Prop) (f : type686 A) : (term249 A s f) = (term299 A s f).
Proof. exact (TRANS (@lem3783124 A s f) (@lem3783154 A s f)). Qed.
Lemma lem3783156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783157 {A : Type'} (s : A -> Prop) (f : type686 A) : (term250 A s f) = (term300 A s f).
Proof. exact (MK_COMB (@lem3783156) (@lem3783155 A s f)). Qed.
Lemma lem3783158 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3783159 {A : Type'} (f : type686 A) (s : A -> Prop) : (term251 A f s) = (term301 A f s).
Proof. exact (MK_COMB (@lem3783157 A s f) (@lem3783158 A s)). Qed.
Lemma lem3783161 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3783162 {A : Type'} (P : type421 A) (Q : Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (@lem3783161 (type1402 A) P Q). Qed.
Lemma lem3783163 {A : Type'} (f : type686 A) (s : A -> Prop) : (term306 A f s) = (term307 A f s).
Proof. exact (@lem3783162 A (term298 A s f) (@FINITE A s)). Qed.
Lemma lem3783164 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term308 A s f t) = (term296 A s f t).
Proof. exact (eq_refl (term308 A s f t)). Qed.
Lemma lem3783165 {A : Type'} (s : A -> Prop) (f : type686 A) : (term309 A s f) = (term298 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783164 A s f t)). Qed.
Lemma lem3783166 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783167 {A : Type'} (s : A -> Prop) (f : type686 A) : (term310 A s f) = (term299 A s f).
Proof. exact (MK_COMB (@lem3783166 A) (@lem3783165 A s f)). Qed.
Lemma lem3783168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783169 {A : Type'} (s : A -> Prop) (f : type686 A) : (term311 A s f) = (term300 A s f).
Proof. exact (MK_COMB (@lem3783168) (@lem3783167 A s f)). Qed.
Lemma lem3783170 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3783171 {A : Type'} (f : type686 A) (s : A -> Prop) : (term306 A f s) = (term301 A f s).
Proof. exact (MK_COMB (@lem3783169 A s f) (@lem3783170 A s)). Qed.
Lemma lem3783172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783173 {A : Type'} (f : type686 A) (s : A -> Prop) : (term312 A f s) = (term313 A f s).
Proof. exact (MK_COMB (@lem3783172) (@lem3783171 A f s)). Qed.
Lemma lem3783174 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term308 A s f t) = (term296 A s f t).
Proof. exact (eq_refl (term308 A s f t)). Qed.
Lemma lem3783175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783176 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term314 A s f t) = (term315 A s f t).
Proof. exact (MK_COMB (@lem3783175) (@lem3783174 A s f t)). Qed.
Lemma lem3783177 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3783178 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term316 A f t s) = (term317 A f t s).
Proof. exact (MK_COMB (@lem3783176 A s f t) (@lem3783177 A s)). Qed.
Lemma lem3783179 {A : Type'} (f : type686 A) (s : A -> Prop) : (term318 A f s) = (term319 A f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783178 A f t s)). Qed.
Lemma lem3783180 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783181 {A : Type'} (f : type686 A) (s : A -> Prop) : (term307 A f s) = (term320 A f s).
Proof. exact (MK_COMB (@lem3783180 A) (@lem3783179 A f s)). Qed.
Lemma lem3783182 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term306 A f s) = (term307 A f s)) = ((term301 A f s) = (term320 A f s)).
Proof. exact (MK_COMB (@lem3783173 A f s) (@lem3783181 A f s)). Qed.
Lemma lem3783183 {A : Type'} (f : type686 A) (s : A -> Prop) : (term301 A f s) = (term320 A f s).
Proof. exact (EQ_MP (@lem3783182 A f s) (@lem3783163 A f s)). Qed.
Lemma lem3783184 {A : Type'} (f : type686 A) (s : A -> Prop) : (term251 A f s) = (term320 A f s).
Proof. exact (TRANS (@lem3783159 A f s) (@lem3783183 A f s)). Qed.
Lemma lem3783185 {A : Type'} (f : type686 A) : (term252 A f) = (term252 A f).
Proof. exact (eq_refl (term252 A f)). Qed.
Lemma lem3783186 {A : Type'} (f : type686 A) (s : A -> Prop) : (term253 A f s) = (term321 A f s).
Proof. exact (MK_COMB (@lem3783185 A f) (@lem3783184 A f s)). Qed.
Lemma lem3783188 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3783189 {A : Type'} (P : type686 A) (Q : Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem3783188 (A -> Prop) P Q). Qed.
Lemma lem3783190 {A : Type'} (f : type686 A) (s : A -> Prop) : (term321 A f s) = (term324 A f s).
Proof. exact (@lem3783189 A f (term320 A f s)). Qed.
Lemma lem3783192 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3783193 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3783192 (type1402 A) P Q). Qed.
Lemma lem3783194 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term329 A x f s) = (term330 A x f s).
Proof. exact (@lem3783193 A (f x) (term319 A f s)). Qed.
Lemma lem3783195 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term331 A f s t) = (term317 A f t s).
Proof. exact (eq_refl (term331 A f s t)). Qed.
Lemma lem3783196 {A : Type'} (f : type686 A) (s : A -> Prop) : (term332 A f s) = (term319 A f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783195 A f t s)). Qed.
Lemma lem3783197 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783198 {A : Type'} (f : type686 A) (s : A -> Prop) : (term333 A f s) = (term320 A f s).
Proof. exact (MK_COMB (@lem3783197 A) (@lem3783196 A f s)). Qed.
Lemma lem3783199 {A : Type'} (f : type686 A) (x : A -> Prop) : (term139 A f x) = (term139 A f x).
Proof. exact (eq_refl (term139 A f x)). Qed.
Lemma lem3783200 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term329 A x f s) = (term334 A x f s).
Proof. exact (MK_COMB (@lem3783199 A f x) (@lem3783198 A f s)). Qed.
Lemma lem3783201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783202 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term335 A x f s) = (term336 A x f s).
Proof. exact (MK_COMB (@lem3783201) (@lem3783200 A x f s)). Qed.
Lemma lem3783203 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term331 A f s t) = (term317 A f t s).
Proof. exact (eq_refl (term331 A f s t)). Qed.
Lemma lem3783204 {A : Type'} (f : type686 A) (x : A -> Prop) : (term139 A f x) = (term139 A f x).
Proof. exact (eq_refl (term139 A f x)). Qed.
Lemma lem3783205 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term337 A x f s t) = (term338 A x f t s).
Proof. exact (MK_COMB (@lem3783204 A f x) (@lem3783203 A f t s)). Qed.
Lemma lem3783206 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term339 A x f s) = (term340 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783205 A x f t s)). Qed.
Lemma lem3783207 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783208 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term330 A x f s) = (term341 A x f s).
Proof. exact (MK_COMB (@lem3783207 A) (@lem3783206 A x f s)). Qed.
Lemma lem3783209 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term329 A x f s) = (term330 A x f s)) = ((term334 A x f s) = (term341 A x f s)).
Proof. exact (MK_COMB (@lem3783202 A x f s) (@lem3783208 A x f s)). Qed.
Lemma lem3783210 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term334 A x f s) = (term341 A x f s).
Proof. exact (EQ_MP (@lem3783209 A x f s) (@lem3783194 A x f s)). Qed.
Lemma lem3783211 {A : Type'} (f : type686 A) (s : A -> Prop) : (term342 A f s) = (term343 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783210 A x f s)). Qed.
Lemma lem3783212 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783213 {A : Type'} (f : type686 A) (s : A -> Prop) : (term324 A f s) = (term344 A f s).
Proof. exact (MK_COMB (@lem3783212 A) (@lem3783211 A f s)). Qed.
Lemma lem3783214 {A : Type'} (f : type686 A) (s : A -> Prop) : (term321 A f s) = (term344 A f s).
Proof. exact (TRANS (@lem3783190 A f s) (@lem3783213 A f s)). Qed.
Lemma lem3783215 {A : Type'} (f : type686 A) (s : A -> Prop) : (term253 A f s) = (term344 A f s).
Proof. exact (TRANS (@lem3783186 A f s) (@lem3783214 A f s)). Qed.
Lemma lem3783216 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3783217 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term345 A f s).
Proof. exact (MK_COMB (@lem3783216 A f) (@lem3783215 A f s)). Qed.
Lemma lem3783219 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3783220 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3783219 (A -> Prop) P Q). Qed.
Lemma lem3783221 {A : Type'} (f : type686 A) (s : A -> Prop) : (term348 A f s) = (term349 A f s).
Proof. exact (@lem3783220 A (term236 A f) (term343 A f s)). Qed.
Lemma lem3783222 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term350 A f s x) = (term341 A x f s).
Proof. exact (eq_refl (term350 A f s x)). Qed.
Lemma lem3783223 {A : Type'} (f : type686 A) (s : A -> Prop) : (term351 A f s) = (term343 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783222 A x f s)). Qed.
Lemma lem3783224 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783225 {A : Type'} (f : type686 A) (s : A -> Prop) : (term352 A f s) = (term344 A f s).
Proof. exact (MK_COMB (@lem3783224 A) (@lem3783223 A f s)). Qed.
Lemma lem3783226 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3783227 {A : Type'} (f : type686 A) (s : A -> Prop) : (term348 A f s) = (term345 A f s).
Proof. exact (MK_COMB (@lem3783226 A f) (@lem3783225 A f s)). Qed.
Lemma lem3783228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783229 {A : Type'} (f : type686 A) (s : A -> Prop) : (term353 A f s) = (term354 A f s).
Proof. exact (MK_COMB (@lem3783228) (@lem3783227 A f s)). Qed.
Lemma lem3783230 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term350 A f s x) = (term341 A x f s).
Proof. exact (eq_refl (term350 A f s x)). Qed.
Lemma lem3783231 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3783232 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term355 A f s x) = (term356 A x f s).
Proof. exact (MK_COMB (@lem3783231 A f) (@lem3783230 A x f s)). Qed.
Lemma lem3783233 {A : Type'} (f : type686 A) (s : A -> Prop) : (term357 A f s) = (term358 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783232 A x f s)). Qed.
Lemma lem3783234 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783235 {A : Type'} (f : type686 A) (s : A -> Prop) : (term349 A f s) = (term359 A f s).
Proof. exact (MK_COMB (@lem3783234 A) (@lem3783233 A f s)). Qed.
Lemma lem3783236 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term348 A f s) = (term349 A f s)) = ((term345 A f s) = (term359 A f s)).
Proof. exact (MK_COMB (@lem3783229 A f s) (@lem3783235 A f s)). Qed.
Lemma lem3783237 {A : Type'} (f : type686 A) (s : A -> Prop) : (term345 A f s) = (term359 A f s).
Proof. exact (EQ_MP (@lem3783236 A f s) (@lem3783221 A f s)). Qed.
Lemma lem3783239 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3783240 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3783239 (type1402 A) P Q). Qed.
Lemma lem3783241 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term360 A x f s) = (term361 A x f s).
Proof. exact (@lem3783240 A (term236 A f) (term340 A x f s)). Qed.
Lemma lem3783242 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term362 A x f s t) = (term338 A x f t s).
Proof. exact (eq_refl (term362 A x f s t)). Qed.
Lemma lem3783243 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term363 A x f s) = (term340 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783242 A x f t s)). Qed.
Lemma lem3783244 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783245 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term364 A x f s) = (term341 A x f s).
Proof. exact (MK_COMB (@lem3783244 A) (@lem3783243 A x f s)). Qed.
Lemma lem3783246 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3783247 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term360 A x f s) = (term356 A x f s).
Proof. exact (MK_COMB (@lem3783246 A f) (@lem3783245 A x f s)). Qed.
Lemma lem3783248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783249 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term365 A x f s) = (term366 A x f s).
Proof. exact (MK_COMB (@lem3783248) (@lem3783247 A x f s)). Qed.
Lemma lem3783250 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term362 A x f s t) = (term338 A x f t s).
Proof. exact (eq_refl (term362 A x f s t)). Qed.
Lemma lem3783251 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3783252 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term367 A x f s t) = (term368 A x f t s).
Proof. exact (MK_COMB (@lem3783251 A f) (@lem3783250 A x f t s)). Qed.
Lemma lem3783253 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term369 A x f s) = (term370 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783252 A x f t s)). Qed.
Lemma lem3783254 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783255 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term361 A x f s) = (term371 A x f s).
Proof. exact (MK_COMB (@lem3783254 A) (@lem3783253 A x f s)). Qed.
Lemma lem3783256 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term360 A x f s) = (term361 A x f s)) = ((term356 A x f s) = (term371 A x f s)).
Proof. exact (MK_COMB (@lem3783249 A x f s) (@lem3783255 A x f s)). Qed.
Lemma lem3783257 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term356 A x f s) = (term371 A x f s).
Proof. exact (EQ_MP (@lem3783256 A x f s) (@lem3783241 A x f s)). Qed.
Lemma lem3783258 {A : Type'} (f : type686 A) (s : A -> Prop) : (term358 A f s) = (term372 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783257 A x f s)). Qed.
Lemma lem3783259 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783260 {A : Type'} (f : type686 A) (s : A -> Prop) : (term359 A f s) = (term373 A f s).
Proof. exact (MK_COMB (@lem3783259 A) (@lem3783258 A f s)). Qed.
Lemma lem3783261 {A : Type'} (f : type686 A) (s : A -> Prop) : (term345 A f s) = (term373 A f s).
Proof. exact (TRANS (@lem3783237 A f s) (@lem3783260 A f s)). Qed.
Lemma lem3783262 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term373 A f s).
Proof. exact (TRANS (@lem3783217 A f s) (@lem3783261 A f s)). Qed.
Lemma lem3783263 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (eq_refl (term138 A t)). Qed.
Lemma lem3783264 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term256 A t f s) = (term374 A t f s).
Proof. exact (MK_COMB (@lem3783263 A t) (@lem3783262 A f s)). Qed.
Lemma lem3783266 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3783267 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3783266 (A -> Prop) P Q). Qed.
Lemma lem3783268 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term375 A t f s) = (term376 A t f s).
Proof. exact (@lem3783267 A (term137 A t) (term372 A f s)). Qed.
Lemma lem3783269 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term377 A f s x) = (term371 A x f s).
Proof. exact (eq_refl (term377 A f s x)). Qed.
Lemma lem3783270 {A : Type'} (f : type686 A) (s : A -> Prop) : (term378 A f s) = (term372 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783269 A x f s)). Qed.
Lemma lem3783271 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783272 {A : Type'} (f : type686 A) (s : A -> Prop) : (term379 A f s) = (term373 A f s).
Proof. exact (MK_COMB (@lem3783271 A) (@lem3783270 A f s)). Qed.
Lemma lem3783273 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (eq_refl (term138 A t)). Qed.
Lemma lem3783274 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term375 A t f s) = (term374 A t f s).
Proof. exact (MK_COMB (@lem3783273 A t) (@lem3783272 A f s)). Qed.
Lemma lem3783275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783276 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term380 A t f s) = (term381 A t f s).
Proof. exact (MK_COMB (@lem3783275) (@lem3783274 A t f s)). Qed.
Lemma lem3783277 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term377 A f s x) = (term371 A x f s).
Proof. exact (eq_refl (term377 A f s x)). Qed.
Lemma lem3783278 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (eq_refl (term138 A t)). Qed.
Lemma lem3783279 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term382 A t f s x) = (term383 A t x f s).
Proof. exact (MK_COMB (@lem3783278 A t) (@lem3783277 A x f s)). Qed.
Lemma lem3783280 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term384 A t f s) = (term385 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783279 A t x f s)). Qed.
Lemma lem3783281 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783282 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term376 A t f s) = (term386 A t f s).
Proof. exact (MK_COMB (@lem3783281 A) (@lem3783280 A t f s)). Qed.
Lemma lem3783283 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : ((term375 A t f s) = (term376 A t f s)) = ((term374 A t f s) = (term386 A t f s)).
Proof. exact (MK_COMB (@lem3783276 A t f s) (@lem3783282 A t f s)). Qed.
Lemma lem3783284 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term374 A t f s) = (term386 A t f s).
Proof. exact (EQ_MP (@lem3783283 A t f s) (@lem3783268 A t f s)). Qed.
Lemma lem3783286 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3783287 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3783286 (type1402 A) P Q). Qed.
Lemma lem3783288 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term387 A t x f s) = (term388 A t x f s).
Proof. exact (@lem3783287 A (term137 A t) (term370 A x f s)). Qed.
Lemma lem3783289 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term389 A x f s t) = (term368 A x f t s).
Proof. exact (eq_refl (term389 A x f s t)). Qed.
Lemma lem3783290 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term390 A x f s) = (term370 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3783289 A x f t s)). Qed.
Lemma lem3783291 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783292 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term391 A x f s) = (term371 A x f s).
Proof. exact (MK_COMB (@lem3783291 A) (@lem3783290 A x f s)). Qed.
Lemma lem3783293 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (eq_refl (term138 A t)). Qed.
Lemma lem3783294 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term387 A t x f s) = (term383 A t x f s).
Proof. exact (MK_COMB (@lem3783293 A t) (@lem3783292 A x f s)). Qed.
Lemma lem3783295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783296 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term392 A t x f s) = (term393 A t x f s).
Proof. exact (MK_COMB (@lem3783295) (@lem3783294 A t x f s)). Qed.
Lemma lem3783297 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term389 A x f s t) = (term368 A x f t s).
Proof. exact (eq_refl (term389 A x f s t)). Qed.
Lemma lem3783298 {A : Type'} (t : type686 A) : (term138 A t) = (term138 A t).
Proof. exact (eq_refl (term138 A t)). Qed.
Lemma lem3783299 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term394 A t x f s t') = (term395 A t x f t' s).
Proof. exact (MK_COMB (@lem3783298 A t) (@lem3783297 A x f t' s)). Qed.
Lemma lem3783300 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term396 A t x f s) = (term397 A t x f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3783299 A t x f t' s)). Qed.
Lemma lem3783301 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3783302 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term388 A t x f s) = (term398 A t x f s).
Proof. exact (MK_COMB (@lem3783301 A) (@lem3783300 A t x f s)). Qed.
Lemma lem3783303 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term387 A t x f s) = (term388 A t x f s)) = ((term383 A t x f s) = (term398 A t x f s)).
Proof. exact (MK_COMB (@lem3783296 A t x f s) (@lem3783302 A t x f s)). Qed.
Lemma lem3783304 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term383 A t x f s) = (term398 A t x f s).
Proof. exact (EQ_MP (@lem3783303 A t x f s) (@lem3783288 A t x f s)). Qed.
Lemma lem3783305 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term385 A t f s) = (term399 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783304 A t x f s)). Qed.
Lemma lem3783306 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3783307 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term386 A t f s) = (term400 A t f s).
Proof. exact (MK_COMB (@lem3783306 A) (@lem3783305 A t f s)). Qed.
Lemma lem3783308 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term374 A t f s) = (term400 A t f s).
Proof. exact (TRANS (@lem3783284 A t f s) (@lem3783307 A t f s)). Qed.
Lemma lem3783310 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term256 A t f s) = (term400 A t f s).
Proof. exact (TRANS (@lem3783264 A t f s) (@lem3783308 A t f s)). Qed.
Lemma lem3783311 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term176 A t f s) = (term400 A t f s).
Proof. exact (TRANS (@lem3782900 A t f s) (@lem3783310 A t f s)). Qed.
Lemma lem3783312 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term176 A t f s) : term400 A t f s.
Proof. exact (EQ_MP (@lem3783311 A t f s) (@lem3782806 A t f s h1)). Qed.
Lemma lem3783314 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term188 A s x).
Proof. exact (eq_refl (term188 A s x)). Qed.
Lemma lem3783315 {A : Type'} (s : A -> Prop) : (term190 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem3783314 A s x)). Qed.
Lemma lem3783316 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783317 {A : Type'} (s : A -> Prop) : (term191 A s) = (term191 A s).
Proof. exact (MK_COMB (@lem3783316 A) (@lem3783315 A s)). Qed.
Lemma lem3783319 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem3783328 {A : Type'} (s : A -> Prop) : (term193 A s) = (term193 A s).
Proof. exact (MK_COMB (@lem3783319 A) (@lem3783317 A s)). Qed.
Lemma lem3783329 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term193 A s.
Proof. exact (EQ_MP (@lem3783328 A s) (@lem3782807 A s h1)). Qed.
Lemma lem3783337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term401 A s t x) = (term402 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3783338 {A : Type'} (P : A -> Prop) : (term403 A P) = (term404 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3783339 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term406 A s t).
Proof. exact (@lem3783338 A (term148 A s t)). Qed.
Lemma lem3783340 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term407 A s t x) = (term146 A s t x).
Proof. exact (eq_refl (term407 A s t x)). Qed.
Lemma lem3783341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783342 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term408 A s t x) = (term401 A s t x).
Proof. exact (MK_COMB (@lem3783341) (@lem3783340 A s t x)). Qed.
Lemma lem3783343 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term408 A s t x) = (term402 A s t x).
Proof. exact (TRANS (@lem3783342 A s t x) (@lem3783337 A s t x)). Qed.
Lemma lem3783344 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term409 A s t) = (term410 A s t).
Proof. exact (fun_ext (fun x : A => @lem3783343 A s t x)). Qed.
Lemma lem3783345 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3783346 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term406 A s t) = (term411 A s t).
Proof. exact (MK_COMB (@lem3783345 A) (@lem3783344 A s t)). Qed.
Lemma lem3783347 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term411 A s t).
Proof. exact (TRANS (@lem3783339 A s t) (@lem3783346 A s t)). Qed.
Lemma lem3783349 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term412 A f t).
Proof. exact (eq_refl (term412 A f t)). Qed.
Lemma lem3783350 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term413 A f s t) = (term414 A f s t).
Proof. exact (MK_COMB (@lem3783349 A f t) (@lem3783347 A s t)). Qed.
Lemma lem3783351 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term415 A f s t) = (term413 A f s t).
Proof. exact (@lem17045 (f t) (term149 A s t)). Qed.
Lemma lem3783352 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term415 A f s t) = (term414 A f s t).
Proof. exact (TRANS (@lem3783351 A f s t) (@lem3783350 A f s t)). Qed.
Lemma lem3783353 {A : Type'} (P : type686 A) : (term416 A P) = (term137 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3783354 {A : Type'} (f : type686 A) (s : A -> Prop) : (term221 A f s) = (term417 A f s).
Proof. exact (@lem3783353 A (term196 A f s)). Qed.
Lemma lem3783355 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term418 A f s t) = (term195 A f s t).
Proof. exact (eq_refl (term418 A f s t)). Qed.
Lemma lem3783356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783357 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term419 A f s t) = (term415 A f s t).
Proof. exact (MK_COMB (@lem3783356) (@lem3783355 A f s t)). Qed.
Lemma lem3783358 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term419 A f s t) = (term414 A f s t).
Proof. exact (TRANS (@lem3783357 A f s t) (@lem3783352 A f s t)). Qed.
Lemma lem3783359 {A : Type'} (f : type686 A) (s : A -> Prop) : (term420 A f s) = (term421 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783358 A f s t)). Qed.
Lemma lem3783360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783361 {A : Type'} (f : type686 A) (s : A -> Prop) : (term417 A f s) = (term422 A f s).
Proof. exact (MK_COMB (@lem3783360 A) (@lem3783359 A f s)). Qed.
Lemma lem3783362 {A : Type'} (f : type686 A) (s : A -> Prop) : (term221 A f s) = (term422 A f s).
Proof. exact (TRANS (@lem3783354 A f s) (@lem3783361 A f s)). Qed.
Lemma lem3783441 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3783442 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem3783441 A P Q). Qed.
Lemma lem3783443 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term423 A f s t) = (term424 A f s t).
Proof. exact (@lem3783442 A (term134 A f t) (term410 A s t)). Qed.
Lemma lem3783444 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term425 A s t x) = (term402 A s t x).
Proof. exact (eq_refl (term425 A s t x)). Qed.
Lemma lem3783445 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term426 A s t) = (term410 A s t).
Proof. exact (fun_ext (fun x : A => @lem3783444 A s t x)). Qed.
Lemma lem3783446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3783447 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term427 A s t) = (term411 A s t).
Proof. exact (MK_COMB (@lem3783446 A) (@lem3783445 A s t)). Qed.
Lemma lem3783448 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term412 A f t).
Proof. exact (eq_refl (term412 A f t)). Qed.
Lemma lem3783449 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term423 A f s t) = (term414 A f s t).
Proof. exact (MK_COMB (@lem3783448 A f t) (@lem3783447 A s t)). Qed.
Lemma lem3783450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783451 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term428 A f s t) = (term429 A f s t).
Proof. exact (MK_COMB (@lem3783450) (@lem3783449 A f s t)). Qed.
Lemma lem3783452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term425 A s t x) = (term402 A s t x).
Proof. exact (eq_refl (term425 A s t x)). Qed.
Lemma lem3783453 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term412 A f t).
Proof. exact (eq_refl (term412 A f t)). Qed.
Lemma lem3783454 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term430 A f s t x) = (term431 A f s t x).
Proof. exact (MK_COMB (@lem3783453 A f t) (@lem3783452 A s t x)). Qed.
Lemma lem3783455 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term432 A f s t) = (term433 A f s t).
Proof. exact (fun_ext (fun x : A => @lem3783454 A f s t x)). Qed.
Lemma lem3783456 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3783457 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term424 A f s t) = (term434 A f s t).
Proof. exact (MK_COMB (@lem3783456 A) (@lem3783455 A f s t)). Qed.
Lemma lem3783458 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : ((term423 A f s t) = (term424 A f s t)) = ((term414 A f s t) = (term434 A f s t)).
Proof. exact (MK_COMB (@lem3783451 A f s t) (@lem3783457 A f s t)). Qed.
Lemma lem3783459 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term414 A f s t) = (term434 A f s t).
Proof. exact (EQ_MP (@lem3783458 A f s t) (@lem3783443 A f s t)). Qed.
Lemma lem3783460 {A : Type'} (f : type686 A) (s : A -> Prop) : (term421 A f s) = (term435 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783459 A f s t)). Qed.
Lemma lem3783461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783462 {A : Type'} (f : type686 A) (s : A -> Prop) : (term422 A f s) = (term436 A f s).
Proof. exact (MK_COMB (@lem3783461 A) (@lem3783460 A f s)). Qed.
Lemma lem3783464 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3783465 {A : Type'} (P : type672 A) : (term437 A P) = (term438 A P).
Proof. exact (@lem3783464 (A -> Prop) A P). Qed.
Lemma lem3783466 {A : Type'} (f : type686 A) (s : A -> Prop) : (term439 A f s) = (term440 A f s).
Proof. exact (@lem3783465 A (term441 A f s)). Qed.
Lemma lem3783467 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term442 A f s t) = (term433 A f s t).
Proof. exact (eq_refl (term442 A f s t)). Qed.
Lemma lem3783468 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3783469 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term443 A f s t x) = (term444 A f s t x).
Proof. exact (MK_COMB (@lem3783467 A f s t) (@lem3783468 A x)). Qed.
Lemma lem3783470 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term444 A f s t x) = (term431 A f s t x).
Proof. exact (eq_refl (term444 A f s t x)). Qed.
Lemma lem3783471 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term443 A f s t x) = (term431 A f s t x).
Proof. exact (TRANS (@lem3783469 A f s t x) (@lem3783470 A f s t x)). Qed.
Lemma lem3783472 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term445 A f s t) = (term433 A f s t).
Proof. exact (fun_ext (fun x : A => @lem3783471 A f s t x)). Qed.
Lemma lem3783473 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3783474 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term446 A f s t) = (term434 A f s t).
Proof. exact (MK_COMB (@lem3783473 A) (@lem3783472 A f s t)). Qed.
Lemma lem3783475 {A : Type'} (f : type686 A) (s : A -> Prop) : (term447 A f s) = (term435 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783474 A f s t)). Qed.
Lemma lem3783476 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783477 {A : Type'} (f : type686 A) (s : A -> Prop) : (term439 A f s) = (term436 A f s).
Proof. exact (MK_COMB (@lem3783476 A) (@lem3783475 A f s)). Qed.
Lemma lem3783478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3783479 {A : Type'} (f : type686 A) (s : A -> Prop) : (term448 A f s) = (term449 A f s).
Proof. exact (MK_COMB (@lem3783478) (@lem3783477 A f s)). Qed.
Lemma lem3783480 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term442 A f s t) = (term433 A f s t).
Proof. exact (eq_refl (term442 A f s t)). Qed.
Lemma lem3783481 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3783482 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term450 A f s x t) = (term451 A f s x t).
Proof. exact (MK_COMB (@lem3783480 A f s t) (@lem3783481 A x t)). Qed.
Lemma lem3783483 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term451 A f s x t) = (term452 A f s x t).
Proof. exact (eq_refl (term451 A f s x t)). Qed.
Lemma lem3783484 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term450 A f s x t) = (term452 A f s x t).
Proof. exact (TRANS (@lem3783482 A f s x t) (@lem3783483 A f s x t)). Qed.
Lemma lem3783485 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term453 A f s x) = (term454 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783484 A f s x t)). Qed.
Lemma lem3783486 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783487 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term455 A f s x) = (term456 A f s x).
Proof. exact (MK_COMB (@lem3783486 A) (@lem3783485 A f s x)). Qed.
Lemma lem3783488 {A : Type'} (f : type686 A) (s : A -> Prop) : (term457 A f s) = (term458 A f s).
Proof. exact (fun_ext (fun x : type684 A => @lem3783487 A f s x)). Qed.
Lemma lem3783489 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3783490 {A : Type'} (f : type686 A) (s : A -> Prop) : (term440 A f s) = (term459 A f s).
Proof. exact (MK_COMB (@lem3783489 A) (@lem3783488 A f s)). Qed.
Lemma lem3783491 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term439 A f s) = (term440 A f s)) = ((term436 A f s) = (term459 A f s)).
Proof. exact (MK_COMB (@lem3783479 A f s) (@lem3783490 A f s)). Qed.
Lemma lem3783492 {A : Type'} (f : type686 A) (s : A -> Prop) : (term436 A f s) = (term459 A f s).
Proof. exact (EQ_MP (@lem3783491 A f s) (@lem3783466 A f s)). Qed.
Lemma lem3783494 {A : Type'} (f : type686 A) (s : A -> Prop) : (term422 A f s) = (term459 A f s).
Proof. exact (TRANS (@lem3783462 A f s) (@lem3783492 A f s)). Qed.
Lemma lem3783495 {A : Type'} (f : type686 A) (s : A -> Prop) : (term221 A f s) = (term459 A f s).
Proof. exact (TRANS (@lem3783362 A f s) (@lem3783494 A f s)). Qed.
Lemma lem3783496 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) : term459 A f s.
Proof. exact (EQ_MP (@lem3783495 A f s) (@lem3782812 A f s h1)). Qed.
Lemma lem3783497 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term456 A f s x.
Proof. exact (h1). Qed.
Lemma lem3783498 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) (h1 : term398 A t x' f s) : term398 A t x' f s.
Proof. exact (h1). Qed.
Lemma lem3783499 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : term395 A t x' f t' s.
Proof. exact (h1). Qed.
Lemma lem3783500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783506 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783505 A Prop f x). Qed.
Lemma lem3783508 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3783506 A s x). Qed.
Lemma lem3783509 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term460 A s x).
Proof. exact (MK_COMB (@lem3783500) (@lem3783508 A s x)). Qed.
Lemma lem3783510 {A : Type'} (s : A -> Prop) : (term190 A s) = (term461 A s).
Proof. exact (fun_ext (fun x : A => @lem3783509 A s x)). Qed.
Lemma lem3783511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783512 {A : Type'} (s : A -> Prop) : (term191 A s) = (term462 A s).
Proof. exact (MK_COMB (@lem3783511 A) (@lem3783510 A s)). Qed.
Lemma lem3783517 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783518 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3783517 (type686 A) Prop f x). Qed.
Lemma lem3783520 {A : Type'} : (@FINITE (A -> Prop) (@EMPTY (A -> Prop))) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) (@EMPTY (A -> Prop))).
Proof. exact (@lem3783518 A (@FINITE (A -> Prop)) (@EMPTY (A -> Prop))). Qed.
Lemma lem3783521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783522 {A : Type'} : (term67 A) = (term463 A).
Proof. exact (MK_COMB (@lem3783521) (@lem3783520 A)). Qed.
Lemma lem3783523 {A : Type'} (s : A -> Prop) : (term193 A s) = (term464 A s).
Proof. exact (MK_COMB (@lem3783522 A) (@lem3783512 A s)). Qed.
Lemma lem3783524 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term464 A s.
Proof. exact (EQ_MP (@lem3783523 A s) (@lem3783329 A s h1)). Qed.
Lemma lem3783525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783526 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3783531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783532 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3783531 (A -> Prop) A f x). Qed.
Lemma lem3783534 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (@I ((A -> Prop) -> A) x t).
Proof. exact (@lem3783532 A x t). Qed.
Lemma lem3783535 {A : Type'} (x : type684 A) (t : A -> Prop) : (term465 A x t) = (term466 A x t).
Proof. exact (MK_COMB (@lem3783526 A t) (@lem3783534 A x t)). Qed.
Lemma lem3783537 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783538 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783537 A Prop f x). Qed.
Lemma lem3783539 {A : Type'} (x : type684 A) (t : A -> Prop) : (term466 A x t) = (term467 A x t).
Proof. exact (@lem3783538 A t (@I ((A -> Prop) -> A) x t)). Qed.
Lemma lem3783540 {A : Type'} (x : type684 A) (t : A -> Prop) : (term465 A x t) = (term467 A x t).
Proof. exact (TRANS (@lem3783535 A x t) (@lem3783539 A x t)). Qed.
Lemma lem3783541 {A : Type'} (x : type684 A) (t : A -> Prop) : (term468 A x t) = (term469 A x t).
Proof. exact (MK_COMB (@lem3783525) (@lem3783540 A x t)). Qed.
Lemma lem3783542 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3783547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783548 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3783547 (A -> Prop) A f x). Qed.
Lemma lem3783550 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (@I ((A -> Prop) -> A) x t).
Proof. exact (@lem3783548 A x t). Qed.
Lemma lem3783551 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term470 A s x t) = (term471 A s x t).
Proof. exact (MK_COMB (@lem3783542 A s) (@lem3783550 A x t)). Qed.
Lemma lem3783553 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783554 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783553 A Prop f x). Qed.
Lemma lem3783555 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term471 A s x t) = (term472 A s x t).
Proof. exact (@lem3783554 A s (@I ((A -> Prop) -> A) x t)). Qed.
Lemma lem3783556 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term470 A s x t) = (term472 A s x t).
Proof. exact (TRANS (@lem3783551 A s x t) (@lem3783555 A s x t)). Qed.
Lemma lem3783557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783558 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term473 A s x t) = (term474 A s x t).
Proof. exact (MK_COMB (@lem3783557) (@lem3783556 A s x t)). Qed.
Lemma lem3783559 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term475 A s x t) = (term476 A s x t).
Proof. exact (MK_COMB (@lem3783558 A s x t) (@lem3783541 A x t)). Qed.
Lemma lem3783560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783566 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783565 (A -> Prop) Prop f x). Qed.
Lemma lem3783568 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3783566 A f t). Qed.
Lemma lem3783569 {A : Type'} (f : type686 A) (t : A -> Prop) : (term134 A f t) = (term477 A f t).
Proof. exact (MK_COMB (@lem3783560) (@lem3783568 A f t)). Qed.
Lemma lem3783570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783571 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term478 A f t).
Proof. exact (MK_COMB (@lem3783570) (@lem3783569 A f t)). Qed.
Lemma lem3783572 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term452 A f s x t) = (term479 A f s x t).
Proof. exact (MK_COMB (@lem3783571 A f t) (@lem3783559 A s x t)). Qed.
Lemma lem3783573 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term454 A f s x) = (term480 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783572 A f s x t)). Qed.
Lemma lem3783574 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783575 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term456 A f s x) = (term481 A f s x).
Proof. exact (MK_COMB (@lem3783574 A) (@lem3783573 A f s x)). Qed.
Lemma lem3783576 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term481 A f s x.
Proof. exact (EQ_MP (@lem3783575 A f s x) (@lem3783497 A f s x h1)). Qed.
Lemma lem3783581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783582 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783581 (A -> Prop) Prop f x). Qed.
Lemma lem3783584 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3783582 A (@FINITE A) s). Qed.
Lemma lem3783591 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783592 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3783591 A (A -> Prop) f x). Qed.
Lemma lem3783593 {A : Type'} (t' : type1402 A) (x : A) : (t' x) = (@I (A -> A -> Prop) t' x).
Proof. exact (@lem3783592 A t' x). Qed.
Lemma lem3783594 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3783595 {A : Type'} (t' : type1402 A) (x : A) : (t' x x) = (@I (A -> A -> Prop) t' x x).
Proof. exact (MK_COMB (@lem3783593 A t' x) (@lem3783594 A x)). Qed.
Lemma lem3783597 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783598 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783597 A Prop f x). Qed.
Lemma lem3783599 {A : Type'} (t' : type1402 A) (x : A) : (@I (A -> A -> Prop) t' x x) = (term482 A t' x).
Proof. exact (@lem3783598 A (@I (A -> A -> Prop) t' x) x). Qed.
Lemma lem3783601 {A : Type'} (t' : type1402 A) (x : A) : (t' x x) = (term482 A t' x).
Proof. exact (TRANS (@lem3783595 A t' x) (@lem3783599 A t' x)). Qed.
Lemma lem3783602 {A : Type'} (f : type686 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3783607 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783608 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3783607 A (A -> Prop) f x). Qed.
Lemma lem3783610 {A : Type'} (t' : type1402 A) (x : A) : (t' x) = (@I (A -> A -> Prop) t' x).
Proof. exact (@lem3783608 A t' x). Qed.
Lemma lem3783611 {A : Type'} (f : type686 A) (t' : type1402 A) (x : A) : (term483 A f t' x) = (term484 A f t' x).
Proof. exact (MK_COMB (@lem3783602 A f) (@lem3783610 A t' x)). Qed.
Lemma lem3783613 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783614 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783613 (A -> Prop) Prop f x). Qed.
Lemma lem3783615 {A : Type'} (f : type686 A) (t' : type1402 A) (x : A) : (term484 A f t' x) = (term485 A f t' x).
Proof. exact (@lem3783614 A f (@I (A -> A -> Prop) t' x)). Qed.
Lemma lem3783616 {A : Type'} (f : type686 A) (t' : type1402 A) (x : A) : (term483 A f t' x) = (term485 A f t' x).
Proof. exact (TRANS (@lem3783611 A f t' x) (@lem3783615 A f t' x)). Qed.
Lemma lem3783617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783618 {A : Type'} (f : type686 A) (t' : type1402 A) (x : A) : (term486 A f t' x) = (term487 A f t' x).
Proof. exact (MK_COMB (@lem3783617) (@lem3783616 A f t' x)). Qed.
Lemma lem3783619 {A : Type'} (f : type686 A) (t' : type1402 A) (x : A) : (term488 A f t' x) = (term489 A f t' x).
Proof. exact (MK_COMB (@lem3783618 A f t' x) (@lem3783601 A t' x)). Qed.
Lemma lem3783620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783626 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783625 A Prop f x). Qed.
Lemma lem3783628 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3783626 A s x). Qed.
Lemma lem3783629 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term460 A s x).
Proof. exact (MK_COMB (@lem3783620) (@lem3783628 A s x)). Qed.
Lemma lem3783630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783631 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term490 A s x).
Proof. exact (MK_COMB (@lem3783630) (@lem3783629 A s x)). Qed.
Lemma lem3783632 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : type1402 A) (x : A) : (term292 A s f t' x) = (term491 A s f t' x).
Proof. exact (MK_COMB (@lem3783631 A s x) (@lem3783619 A f t' x)). Qed.
Lemma lem3783633 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : type1402 A) : (term294 A s f t') = (term492 A s f t').
Proof. exact (fun_ext (fun x : A => @lem3783632 A s f t' x)). Qed.
Lemma lem3783634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783635 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : type1402 A) : (term296 A s f t') = (term493 A s f t').
Proof. exact (MK_COMB (@lem3783634 A) (@lem3783633 A s f t')). Qed.
Lemma lem3783636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783637 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : type1402 A) : (term315 A s f t') = (term494 A s f t').
Proof. exact (MK_COMB (@lem3783636) (@lem3783635 A s f t')). Qed.
Lemma lem3783638 {A : Type'} (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term317 A f t' s) = (term495 A f t' s).
Proof. exact (MK_COMB (@lem3783637 A s f t') (@lem3783584 A s)). Qed.
Lemma lem3783643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783644 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783643 (A -> Prop) Prop f x). Qed.
Lemma lem3783646 {A : Type'} (f : type686 A) (x' : A -> Prop) : (f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3783644 A f x'). Qed.
Lemma lem3783647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783648 {A : Type'} (f : type686 A) (x' : A -> Prop) : (term139 A f x') = (term496 A f x').
Proof. exact (MK_COMB (@lem3783647) (@lem3783646 A f x')). Qed.
Lemma lem3783649 {A : Type'} (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term338 A x' f t' s) = (term497 A x' f t' s).
Proof. exact (MK_COMB (@lem3783648 A f x') (@lem3783638 A f t' s)). Qed.
Lemma lem3783654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783655 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783654 A Prop f x). Qed.
Lemma lem3783657 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3783655 A t x). Qed.
Lemma lem3783658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783664 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783663 A Prop f x). Qed.
Lemma lem3783666 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3783664 A u x). Qed.
Lemma lem3783667 {A : Type'} (u : A -> Prop) (x : A) : (term188 A u x) = (term460 A u x).
Proof. exact (MK_COMB (@lem3783658) (@lem3783666 A u x)). Qed.
Lemma lem3783668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783669 {A : Type'} (u : A -> Prop) (x : A) : (term246 A u x) = (term490 A u x).
Proof. exact (MK_COMB (@lem3783668) (@lem3783667 A u x)). Qed.
Lemma lem3783670 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term224 A u t x) = (term498 A u t x).
Proof. exact (MK_COMB (@lem3783669 A u x) (@lem3783657 A t x)). Qed.
Lemma lem3783671 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term225 A u t) = (term499 A u t).
Proof. exact (fun_ext (fun x : A => @lem3783670 A u t x)). Qed.
Lemma lem3783672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783673 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term226 A u t) = (term500 A u t).
Proof. exact (MK_COMB (@lem3783672 A) (@lem3783671 A u t)). Qed.
Lemma lem3783678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783679 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783678 A Prop f x). Qed.
Lemma lem3783681 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3783679 A u x). Qed.
Lemma lem3783682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783688 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3783687 A Prop f x). Qed.
Lemma lem3783690 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3783688 A t x). Qed.
Lemma lem3783691 {A : Type'} (t : A -> Prop) (x : A) : (term188 A t x) = (term460 A t x).
Proof. exact (MK_COMB (@lem3783682) (@lem3783690 A t x)). Qed.
Lemma lem3783692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783693 {A : Type'} (t : A -> Prop) (x : A) : (term246 A t x) = (term490 A t x).
Proof. exact (MK_COMB (@lem3783692) (@lem3783691 A t x)). Qed.
Lemma lem3783694 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term224 A t u x) = (term498 A t u x).
Proof. exact (MK_COMB (@lem3783693 A t x) (@lem3783681 A u x)). Qed.
Lemma lem3783695 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term225 A t u) = (term499 A t u).
Proof. exact (fun_ext (fun x : A => @lem3783694 A t u x)). Qed.
Lemma lem3783696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783697 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term226 A t u) = (term500 A t u).
Proof. exact (MK_COMB (@lem3783696 A) (@lem3783695 A t u)). Qed.
Lemma lem3783698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783699 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term227 A t u) = (term501 A t u).
Proof. exact (MK_COMB (@lem3783698) (@lem3783697 A t u)). Qed.
Lemma lem3783700 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term228 A u t) = (term502 A u t).
Proof. exact (MK_COMB (@lem3783699 A t u) (@lem3783673 A u t)). Qed.
Lemma lem3783701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783707 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783706 (A -> Prop) Prop f x). Qed.
Lemma lem3783709 {A : Type'} (f : type686 A) (u : A -> Prop) : (f u) = (@I ((A -> Prop) -> Prop) f u).
Proof. exact (@lem3783707 A f u). Qed.
Lemma lem3783710 {A : Type'} (f : type686 A) (u : A -> Prop) : (term134 A f u) = (term477 A f u).
Proof. exact (MK_COMB (@lem3783701) (@lem3783709 A f u)). Qed.
Lemma lem3783711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783717 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783716 (A -> Prop) Prop f x). Qed.
Lemma lem3783719 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3783717 A f t). Qed.
Lemma lem3783720 {A : Type'} (f : type686 A) (t : A -> Prop) : (term134 A f t) = (term477 A f t).
Proof. exact (MK_COMB (@lem3783711) (@lem3783719 A f t)). Qed.
Lemma lem3783721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783722 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term478 A f t).
Proof. exact (MK_COMB (@lem3783721) (@lem3783720 A f t)). Qed.
Lemma lem3783723 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term223 A t f u) = (term503 A t f u).
Proof. exact (MK_COMB (@lem3783722 A f t) (@lem3783710 A f u)). Qed.
Lemma lem3783724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3783725 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term230 A t f u) = (term504 A t f u).
Proof. exact (MK_COMB (@lem3783724) (@lem3783723 A t f u)). Qed.
Lemma lem3783726 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term232 A f u t) = (term505 A f u t).
Proof. exact (MK_COMB (@lem3783725 A t f u) (@lem3783700 A u t)). Qed.
Lemma lem3783727 {A : Type'} (f : type686 A) (t : A -> Prop) : (term233 A f t) = (term506 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3783726 A f u t)). Qed.
Lemma lem3783728 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783729 {A : Type'} (f : type686 A) (t : A -> Prop) : (term234 A f t) = (term507 A f t).
Proof. exact (MK_COMB (@lem3783728 A) (@lem3783727 A f t)). Qed.
Lemma lem3783730 {A : Type'} (f : type686 A) : (term235 A f) = (term508 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783729 A f t)). Qed.
Lemma lem3783731 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783732 {A : Type'} (f : type686 A) : (term236 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3783731 A) (@lem3783730 A f)). Qed.
Lemma lem3783733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783734 {A : Type'} (f : type686 A) : (term254 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3783733) (@lem3783732 A f)). Qed.
Lemma lem3783735 {A : Type'} (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term368 A x' f t' s) = (term511 A x' f t' s).
Proof. exact (MK_COMB (@lem3783734 A f) (@lem3783649 A x' f t' s)). Qed.
Lemma lem3783736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3783741 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3783742 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3783741 (A -> Prop) Prop f x). Qed.
Lemma lem3783744 {A : Type'} (t : type686 A) (x : A -> Prop) : (t x) = (@I ((A -> Prop) -> Prop) t x).
Proof. exact (@lem3783742 A t x). Qed.
Lemma lem3783745 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term477 A t x).
Proof. exact (MK_COMB (@lem3783736) (@lem3783744 A t x)). Qed.
Lemma lem3783746 {A : Type'} (t : type686 A) : (term136 A t) = (term512 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3783745 A t x)). Qed.
Lemma lem3783747 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783748 {A : Type'} (t : type686 A) : (term137 A t) = (term513 A t).
Proof. exact (MK_COMB (@lem3783747 A) (@lem3783746 A t)). Qed.
Lemma lem3783749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3783750 {A : Type'} (t : type686 A) : (term138 A t) = (term514 A t).
Proof. exact (MK_COMB (@lem3783749) (@lem3783748 A t)). Qed.
Lemma lem3783751 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term395 A t x' f t' s) = (term515 A t x' f t' s).
Proof. exact (MK_COMB (@lem3783750 A t) (@lem3783735 A x' f t' s)). Qed.
Lemma lem3783752 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : term515 A t x' f t' s.
Proof. exact (EQ_MP (@lem3783751 A t x' f t' s) (@lem3783499 A t x' f t' s h1)). Qed.
Lemma lem3783753 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : term511 A x' f t' s.
Proof. exact (proj2 (@lem3783752 A t x' f t' s h1)). Qed.
Lemma lem3783755 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : term497 A x' f t' s.
Proof. exact (proj2 (@lem3783753 A t x' f t' s h1)). Qed.
Lemma lem3783761 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term462 A s.
Proof. exact (proj2 (@lem3783524 A s h1)). Qed.
Lemma lem3783780 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) (t : A -> Prop) : (term479 A f s x t) = (term516 A s f x t).
Proof. exact (@lem19490 (term472 A s x t) (term477 A f t) (term469 A x t)). Qed.
Lemma lem3783781 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) : (term480 A f s x) = (term517 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3783780 A s f x t)). Qed.
Lemma lem3783782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3783784 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) : (term481 A f s x) = (term518 A s f x).
Proof. exact (MK_COMB (@lem3783782 A) (@lem3783781 A s f x)). Qed.
Lemma lem3783785 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term518 A s f x.
Proof. exact (EQ_MP (@lem3783784 A s f x) (@lem3783576 A f s x h1)). Qed.
Lemma lem3783975 {A : Type'} (s : A -> Prop) (x : A) : (term460 A s x) = (term460 A s x).
Proof. exact (eq_refl (term460 A s x)). Qed.
Lemma lem3783976 {A : Type'} (s : A -> Prop) : (term461 A s) = (term461 A s).
Proof. exact (fun_ext (fun x : A => @lem3783975 A s x)). Qed.
Lemma lem3783977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3783979 {A : Type'} (s : A -> Prop) : (term462 A s) = (term462 A s).
Proof. exact (MK_COMB (@lem3783977 A) (@lem3783976 A s)). Qed.
Lemma lem3783980 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term462 A s.
Proof. exact (EQ_MP (@lem3783979 A s) (@lem3783761 A s h1)). Qed.
Lemma lem3783981 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term519 A s f x _43447.
Proof. exact (@lem3783785 A f s x h1 _43447). Qed.
Lemma lem3783982 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) (_43447 : A -> Prop) : (term519 A s f x _43447) = (term516 A s f x _43447).
Proof. exact (eq_refl (term519 A s f x _43447)). Qed.
Lemma lem3783983 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term516 A s f x _43447.
Proof. exact (EQ_MP (@lem3783982 A s f x _43447) (@lem3783981 A _43447 f s x h1)). Qed.
Lemma lem3784002 {A : Type'} (_43454 : A) (s : A -> Prop) (h1 : term193 A s) : term520 A s _43454.
Proof. exact (@lem3783980 A s h1 _43454). Qed.
Lemma lem3784003 {A : Type'} (s : A -> Prop) (_43454 : A) : (term520 A s _43454) = (term460 A s _43454).
Proof. exact (eq_refl (term520 A s _43454)). Qed.
Lemma lem3784044 {A : Type'} (_43454 : A) (s : A -> Prop) (h1 : term193 A s) : term460 A s _43454.
Proof. exact (EQ_MP (@lem3784003 A s _43454) (@lem3784002 A _43454 s h1)). Qed.
Lemma lem3784062 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term521 A f s x _43447.
Proof. exact (proj1 (@lem3783983 A _43447 f s x h1)). Qed.
Lemma lem3784070 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (proj1 (@lem3783755 A t x' f t' s h1)). Qed.
Lemma lem3784071 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : term522 A f x'.
Proof. exact (fun h0 : term477 A f x' => @lem3784070 A t x' f t' s h1). Qed.
Lemma lem3784073 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3784074 {A : Type'} (f : type686 A) (x' : A -> Prop) : (term522 A f x') = (@I ((A -> Prop) -> Prop) f x').
Proof. exact (@lem3784073 (@I ((A -> Prop) -> Prop) f x')). Qed.
Lemma lem3784075 {A : Type'} (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term395 A t x' f t' s) : @I ((A -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem3784074 A f x') (@lem3784071 A t x' f t' s h1)). Qed.
Lemma lem3784081 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3784082 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : (term521 A f s x _43447) = (term524 A s x f _43447).
Proof. exact (@lem3784081 (term472 A s x _43447) (term477 A f _43447)). Qed.
Lemma lem3784088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3784089 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : (term525 A f s x _43447) = (term526 A s x f _43447).
Proof. exact (MK_COMB (@lem3784088) (@lem3784082 A s x f _43447)). Qed.
Lemma lem3784095 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : (term524 A s x f _43447) = (term524 A s x f _43447).
Proof. exact (eq_refl (term524 A s x f _43447)). Qed.
Lemma lem3784096 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : ((term521 A f s x _43447) = (term524 A s x f _43447)) = ((term524 A s x f _43447) = (term524 A s x f _43447)).
Proof. exact (MK_COMB (@lem3784089 A s x f _43447) (@lem3784095 A s x f _43447)). Qed.
Lemma lem3784098 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3784099 (x : Prop) : (x = x) = True.
Proof. exact (@lem3784098 Prop x). Qed.
Lemma lem3784100 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : ((term524 A s x f _43447) = (term524 A s x f _43447)) = True.
Proof. exact (@lem3784099 (term524 A s x f _43447)). Qed.
Lemma lem3784101 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : ((term521 A f s x _43447) = (term524 A s x f _43447)) = True.
Proof. exact (TRANS (@lem3784096 A s x f _43447) (@lem3784100 A s x f _43447)). Qed.
Lemma lem3784102 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : True = ((term521 A f s x _43447) = (term524 A s x f _43447)).
Proof. exact (SYM (@lem3784101 A s x f _43447)). Qed.
Lemma lem3784103 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43447 : A -> Prop) : (term521 A f s x _43447) = (term524 A s x f _43447).
Proof. exact (EQ_MP (@lem3784102 A s x f _43447) (@lem0)). Qed.
Lemma lem3784104 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term524 A s x f _43447.
Proof. exact (EQ_MP (@lem3784103 A s x f _43447) (@lem3784062 A _43447 f s x h1)). Qed.
Lemma lem3784106 (b : Prop) (a : Prop) : (a \/ b) = (term527 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3784107 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43447 : A -> Prop) : (term524 A s x f _43447) = (term528 A f s x _43447).
Proof. exact (@lem3784106 (term477 A f _43447) (term472 A s x _43447)). Qed.
Lemma lem3784109 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3784110 {A : Type'} (f : type686 A) (_43447 : A -> Prop) : (term529 A f _43447) = (@I ((A -> Prop) -> Prop) f _43447).
Proof. exact (@lem3784109 (@I ((A -> Prop) -> Prop) f _43447)). Qed.
Lemma lem3784111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784112 {A : Type'} (f : type686 A) (_43447 : A -> Prop) : (term530 A f _43447) = (term531 A f _43447).
Proof. exact (MK_COMB (@lem3784111) (@lem3784110 A f _43447)). Qed.
Lemma lem3784113 {A : Type'} (s : A -> Prop) (x : type684 A) (_43447 : A -> Prop) : (term472 A s x _43447) = (term472 A s x _43447).
Proof. exact (eq_refl (term472 A s x _43447)). Qed.
Lemma lem3784114 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43447 : A -> Prop) : (term528 A f s x _43447) = (term532 A f s x _43447).
Proof. exact (MK_COMB (@lem3784112 A f _43447) (@lem3784113 A s x _43447)). Qed.
Lemma lem3784115 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43447 : A -> Prop) : (term524 A s x f _43447) = (term532 A f s x _43447).
Proof. exact (TRANS (@lem3784107 A f s x _43447) (@lem3784114 A f s x _43447)). Qed.
Lemma lem3784118 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term532 A f s x _43447.
Proof. exact (EQ_MP (@lem3784115 A f s x _43447) (@lem3784104 A _43447 f s x h1)). Qed.
Lemma lem3784119 {A : Type'} (_43447 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term532 A f s x _43447.
Proof. exact (@lem3784118 A _43447 f s x h1). Qed.
Lemma lem3784120 {A : Type'} (x' : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term456 A f s x) : term532 A f s x x'.
Proof. exact (@lem3784119 A x' f s x h1). Qed.
Lemma lem3784123 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) : term472 A s x x'.
Proof. exact (@lem3784120 A x' f s x h1 (@lem3784075 A t x' f t' s h2)). Qed.
Lemma lem3784124 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) : term533 A s x x'.
Proof. exact (fun h0 : term534 A s x x' => @lem3784123 A x t x' f t' s h1 h2). Qed.
Lemma lem3784126 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3784127 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term533 A s x x') = (term472 A s x x').
Proof. exact (@lem3784126 (term472 A s x x')). Qed.
Lemma lem3784128 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) : term472 A s x x'.
Proof. exact (EQ_MP (@lem3784127 A s x x') (@lem3784124 A x t x' f t' s h1 h2)). Qed.
Lemma lem3784131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3784133 {A : Type'} (s : A -> Prop) (_43454 : A) : (term460 A s _43454) = (term535 A s _43454).
Proof. exact (@lem3784131 (@I (A -> Prop) s _43454)). Qed.
Lemma lem3784136 {A : Type'} (_43454 : A) (s : A -> Prop) (h1 : term193 A s) : term535 A s _43454.
Proof. exact (EQ_MP (@lem3784133 A s _43454) (@lem3784044 A _43454 s h1)). Qed.
Lemma lem3784137 {A : Type'} (_43454 : A) (s : A -> Prop) (h1 : term193 A s) : term535 A s _43454.
Proof. exact (@lem3784136 A _43454 s h1). Qed.
Lemma lem3784138 {A : Type'} (x : type684 A) (x' : A -> Prop) (s : A -> Prop) (h1 : term193 A s) : term536 A s x x'.
Proof. exact (@lem3784137 A (@I ((A -> Prop) -> A) x x') s h1). Qed.
Lemma lem3784141 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) (h3 : term193 A s) : False.
Proof. exact (@lem3784138 A x x' s h3 (@lem3784128 A x t x' f t' s h1 h2)). Qed.
Lemma lem3784142 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) (h3 : term193 A s) : term537.
Proof. exact (fun h0 : ~ False => @lem3784141 A x t x' f t' s h1 h2 h3). Qed.
Lemma lem3784144 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3784145 : term537 = False.
Proof. exact (@lem3784144 False). Qed.
Lemma lem3784146 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term395 A t x' f t' s) (h3 : term193 A s) : False.
Proof. exact (EQ_MP (@lem3784145) (@lem3784142 A x t x' f t' s h1 h2 h3)). Qed.
Lemma lem3784147 {A : Type'} (x : type684 A) (t : type686 A) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term398 A t x' f s) (h3 : term193 A s) : False.
Proof. exact (ex_elim (@lem3783498 A t x' f s h2) (fun t' : type1402 A => fun h0 : term397 A t x' f s t' => @lem3784146 A x t x' f t' s h1 h0 h3)). Qed.
Lemma lem3784148 {A : Type'} (x : type684 A) (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term456 A f s x) (h2 : term176 A t f s) (h3 : term193 A s) : False.
Proof. exact (ex_elim (@lem3783312 A t f s h2) (fun x' : A -> Prop => fun h0 : term399 A t f s x' => @lem3784147 A x t x' f s h1 h0 h3)). Qed.
Lemma lem3784149 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) (h2 : term176 A t f s) (h3 : term193 A s) : False.
Proof. exact (ex_elim (@lem3783496 A f s h1) (fun x : type684 A => fun h0 : term458 A f s x => @lem3784148 A x t f s h0 h2 h3)). Qed.
Lemma lem3784150 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) (h2 : term176 A t f s) (h3 : term193 A s) : (term193 A s) = False.
Proof. exact (prop_ext (fun h4 : term193 A s => @lem3784149 A t f s h1 h2 h3) (fun h4 : False => @lem3783329 A s h3)). Qed.
Lemma lem3784151 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) (h2 : term176 A t f s) (h3 : term193 A s) : False.
Proof. exact (EQ_MP (@lem3784150 A t f s h1 h2 h3) (@lem3783329 A s h3)). Qed.
Lemma lem3784152 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) (h2 : term176 A t f s) (h3 : term193 A s) : (term221 A f s) = False.
Proof. exact (prop_ext (fun h4 : term221 A f s => @lem3784151 A t f s h1 h2 h3) (fun h4 : False => @lem3782812 A f s h1)). Qed.
Lemma lem3784153 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term221 A f s) (h2 : term176 A t f s) (h3 : term193 A s) : False.
Proof. exact (EQ_MP (@lem3784152 A t f s h1 h2 h3) (@lem3782812 A f s h1)). Qed.
Lemma lem3784154 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term176 A t f s) (h2 : term193 A s) : term220 A f s.
Proof. exact (fun h0 : term221 A f s => @lem3784153 A t f s h0 h1 h2). Qed.
Lemma lem3784155 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term176 A t f s) (h2 : term193 A s) : term197 A f s.
Proof. exact (EQ_MP (@lem3782811 A f s) (@lem3784154 A t f s h1 h2)). Qed.
Lemma lem3784156 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term176 A t f s) : term198 A f s.
Proof. exact (fun h0 : term193 A s => @lem3784155 A t f s h1 h0). Qed.
Lemma lem3784157 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term199 A t f s.
Proof. exact (fun h0 : term176 A t f s => @lem3784156 A t f s h0). Qed.
Lemma lem3784162 {A : Type'} (f : type686 A) (s : A -> Prop) : term211 A f s.
Proof. exact (fun t : type686 A => @lem3784157 A t f s). Qed.
Lemma lem3784167 {A : Type'} (s : A -> Prop) : term215 A s.
Proof. exact (fun f : type686 A => @lem3784162 A f s). Qed.
Lemma lem3784172 {A : Type'} : term219 A.
Proof. exact (fun s : A -> Prop => @lem3784167 A s). Qed.
Lemma lem3784173 {A : Type'} : term218 A.
Proof. exact (EQ_MP (@lem3782805 A) (@lem3784172 A)). Qed.
Lemma lem3784174 {A : Type'} (s : A -> Prop) : term538 A s.
Proof. exact (@lem3784173 A s). Qed.
Lemma lem3784175 {A : Type'} (s : A -> Prop) : (term538 A s) = (term214 A s).
Proof. exact (eq_refl (term538 A s)). Qed.
Lemma lem3784176 {A : Type'} (s : A -> Prop) : term214 A s.
Proof. exact (EQ_MP (@lem3784175 A s) (@lem3784174 A s)). Qed.
Lemma lem3784177 {A : Type'} (s : A -> Prop) (f : type686 A) : term539 A s f.
Proof. exact (@lem3784176 A s f). Qed.
Lemma lem3784178 {A : Type'} (f : type686 A) (s : A -> Prop) : (term539 A s f) = (term210 A f s).
Proof. exact (eq_refl (term539 A s f)). Qed.
Lemma lem3784179 {A : Type'} (f : type686 A) (s : A -> Prop) : term210 A f s.
Proof. exact (EQ_MP (@lem3784178 A f s) (@lem3784177 A s f)). Qed.
Lemma lem3784180 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term540 A f s t.
Proof. exact (@lem3784179 A f s t). Qed.
Lemma lem3784181 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term540 A f s t) = (term201 A t f s).
Proof. exact (eq_refl (term540 A f s t)). Qed.
Lemma lem3784182 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term201 A t f s.
Proof. exact (EQ_MP (@lem3784181 A t f s) (@lem3784180 A f s t)). Qed.
Lemma lem3784184 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term201 A t f s.
Proof. exact (@lem3782402 A t f s (@lem3784182 A t f s)). Qed.
Lemma lem3784185 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term202 A t f s) : False.
Proof. exact (@lem3784184 A t f s (@lem3782386 A t f s h1)). Qed.
Lemma lem3784186 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term202 A t f s) : (term202 A t f s) = False.
Proof. exact (prop_ext (fun h2 : term202 A t f s => @lem3784185 A t f s h1) (fun h2 : False => @lem3782386 A t f s h1)). Qed.
Lemma lem3784187 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term202 A t f s) : False.
Proof. exact (EQ_MP (@lem3784186 A t f s h1) (@lem3782386 A t f s h1)). Qed.
Lemma lem3784188 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term201 A t f s.
Proof. exact (fun h0 : term202 A t f s => @lem3784187 A t f s h0). Qed.
Lemma lem3784189 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term199 A t f s.
Proof. exact (EQ_MP (@lem3782385 A t f s) (@lem3784188 A t f s)). Qed.
Lemma lem3784190 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term131 A t f s.
Proof. exact (EQ_MP (@lem3782381 A t f s) (@lem3784189 A t f s)). Qed.
Lemma lem3784191 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : term130 A t f s.
Proof. exact (EQ_MP (@lem3782003 A t f s) (@lem3784190 A t f s)). Qed.
Lemma lem3784192 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : t = (@EMPTY (A -> Prop))) (h5 : term22 A s f) : term77 A f s.
Proof. exact (@lem3784191 A t f s (@lem3781803 A t s f h1 h2 h3 h4 h5)). Qed.
Lemma lem3784193 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : t = (@EMPTY (A -> Prop))) (h5 : term22 A s f) : term54 A t f s.
Proof. exact (EQ_MP (@lem3781789 A f s t h4) (@lem3784192 A t s f h1 h2 h3 h4 h5)). Qed.
Lemma lem3784194 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term45 A f s t) : term45 A f s t.
Proof. exact (h1). Qed.
Lemma lem3784195 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term70 A f s t) : term70 A f s t.
Proof. exact (h1). Qed.
Lemma lem3784196 {A : Type'} (t : type686 A) (h1 : @FINITE (A -> Prop) t) : @FINITE (A -> Prop) t.
Proof. exact (h1). Qed.
Lemma lem3784197 {A : Type'} (s : A -> Prop) (t : type686 A) (h1 : term22 A s t) : term22 A s t.
Proof. exact (h1). Qed.
Lemma lem3784198 {A : Type'} (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : @SUBSET (A -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3784241 {A : Type'} (s : A -> Prop) (t : type686 A) : (term22 A s t) = ((term22 A s t) = True).
Proof. exact (@lem7 (term22 A s t)). Qed.
Lemma lem3784246 {A : Type'} (s : A -> Prop) (t : type686 A) (h1 : term22 A s t) : (term22 A s t) = True.
Proof. exact (EQ_MP (@lem3784241 A s t) (@lem3784197 A s t h1)). Qed.
Lemma lem3784247 {A : Type'} (t : type686 A) (f : type686 A) : (term541 A t f) = (term541 A t f).
Proof. exact (eq_refl (term541 A t f)). Qed.
Lemma lem3784248 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term22 A s t) : (term542 A f s t) = (term543 A t f).
Proof. exact (MK_COMB (@lem3784247 A t f) (@lem3784246 A s t h1)). Qed.
Lemma lem3784250 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3784251 {A : Type'} (t : type686 A) (f : type686 A) : (term543 A t f) = (term544 A t f).
Proof. exact (@lem3784250 (term544 A t f)). Qed.
Lemma lem3784252 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term22 A s t) : (term542 A f s t) = (term544 A t f).
Proof. exact (TRANS (@lem3784248 A f s t h1) (@lem3784251 A t f)). Qed.
Lemma lem3784253 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term22 A s t) : (term544 A t f) = (term542 A f s t).
Proof. exact (SYM (@lem3784252 A f s t h1)). Qed.
Lemma lem3784284 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3781477 A s t) (@lem3781476 A s t)). Qed.
Lemma lem3784285 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem3784284 (A -> Prop) s t). Qed.
Lemma lem3784286 {A : Type'} (t : type686 A) (f : type686 A) : (@SUBSET (A -> Prop) t f) = (term115 A t f).
Proof. exact (@lem3784285 A t f). Qed.
Lemma lem3784293 {A : Type'} (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term115 A t f.
Proof. exact (EQ_MP (@lem3784286 A t f) (@lem3784198 A t f h1)). Qed.
Lemma lem3784294 {A : Type'} (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term115 A t f.
Proof. exact (h1). Qed.
Lemma lem3784295 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term545 A t f x.
Proof. exact (@lem3784294 A t f h1 x). Qed.
Lemma lem3784296 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) : (term545 A t f x) = (term546 A t x f).
Proof. exact (eq_refl (term545 A t f x)). Qed.
Lemma lem3784297 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term546 A t x f.
Proof. exact (EQ_MP (@lem3784296 A t x f) (@lem3784295 A x t f h1)). Qed.
Lemma lem3784298 {A : Type'} (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : @IN (A -> Prop) x t.
Proof. exact (h1). Qed.
Lemma lem3784299 {A : Type'} (f : type686 A) (x : A -> Prop) (t : type686 A) (h1 : term115 A t f) (h2 : @IN (A -> Prop) x t) : @IN (A -> Prop) x f.
Proof. exact (@lem3784297 A x t f h1 (@lem3784298 A x t h2)). Qed.
Lemma lem3784300 {A : Type'} (f : type686 A) (x : A -> Prop) (t : type686 A) (h1 : @IN (A -> Prop) x t) : term547 A t x f.
Proof. exact (fun h0 : term115 A t f => @lem3784299 A f x t h0 h1). Qed.
Lemma lem3784301 {A : Type'} (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term115 A t f.
Proof. exact (h1). Qed.
Lemma lem3784302 {A : Type'} (f : type686 A) (x : A -> Prop) (t : type686 A) (h1 : term115 A t f) (h2 : @IN (A -> Prop) x t) : @IN (A -> Prop) x f.
Proof. exact (@lem3784300 A f x t h2 (@lem3784301 A t f h1)). Qed.
Lemma lem3784303 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term546 A t x f.
Proof. exact (fun h0 : @IN (A -> Prop) x t => @lem3784302 A f x t h1 h0). Qed.
Lemma lem3784304 {A : Type'} (t : type686 A) (f : type686 A) (h1 : term115 A t f) : term115 A t f.
Proof. exact (fun x : A -> Prop => @lem3784303 A x t f h1). Qed.
Lemma lem3784305 {A : Type'} (t : type686 A) (f : type686 A) : term548 A t f.
Proof. exact (fun h0 : term115 A t f => @lem3784304 A t f h0). Qed.
Lemma lem3784306 {A : Type'} (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term115 A t f.
Proof. exact (@lem3784305 A t f (@lem3784293 A t f h1)). Qed.
Lemma lem3784307 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term545 A t f x.
Proof. exact (@lem3784306 A t f h1 x). Qed.
Lemma lem3784308 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) : (term545 A t f x) = (term546 A t x f).
Proof. exact (eq_refl (term545 A t f x)). Qed.
Lemma lem3784311 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term546 A t x f.
Proof. exact (EQ_MP (@lem3784308 A t x f) (@lem3784307 A x t f h1)). Qed.
Lemma lem3784312 {A : Type'} (x : A -> Prop) (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term546 A t x f.
Proof. exact (@lem3784311 A x t f h1). Qed.
Lemma lem3784313 {A : Type'} (t : type686 A) (f : type686 A) (h1 : @SUBSET (A -> Prop) t f) : term549 A t f.
Proof. exact (@lem3784312 A (@UNIONS A t) t f h1). Qed.
Lemma lem3784315 {A : Type'} (f : type686 A) : term2 A f.
Proof. exact (EQ_MP (@lem3781471 A f) (@lem3781470 A f)). Qed.
Lemma lem3784316 {A : Type'} (f : type686 A) : term2 A f.
Proof. exact (@lem3784315 A f). Qed.
Lemma lem3784317 {A : Type'} (t : type686 A) : term2 A t.
Proof. exact (@lem3784316 A t). Qed.
Lemma lem3784318 (t1 : Prop) : term550 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3784319 (t1 : Prop) : (term550 t1) = (term551 t1).
Proof. exact (eq_refl (term550 t1)). Qed.
Lemma lem3784320 (t1 : Prop) : term551 t1.
Proof. exact (EQ_MP (@lem3784319 t1) (@lem3784318 t1)). Qed.
Lemma lem3784321 (t1 : Prop) (t2 : Prop) : term552 t1 t2.
Proof. exact (@lem3784320 t1 t2). Qed.
Lemma lem3784322 (t1 : Prop) (t2 : Prop) : (term552 t1 t2) = (term553 t1 t2).
Proof. exact (eq_refl (term552 t1 t2)). Qed.
Lemma lem3784323 (t1 : Prop) (t2 : Prop) : term553 t1 t2.
Proof. exact (EQ_MP (@lem3784322 t1 t2) (@lem3784321 t1 t2)). Qed.
Lemma lem3784324 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term554 t1 t2 t3.
Proof. exact (@lem3784323 t1 t2 t3). Qed.
Lemma lem3784325 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term554 t1 t2 t3) = ((term555 t1 t2 t3) = (term556 t1 t2 t3)).
Proof. exact (eq_refl (term554 t1 t2 t3)). Qed.
Lemma lem3784326 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term555 t1 t2 t3) = (term556 t1 t2 t3).
Proof. exact (EQ_MP (@lem3784325 t1 t2 t3) (@lem3784324 t1 t2 t3)). Qed.
Lemma lem3784327 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term556 t1 t2 t3) = (term555 t1 t2 t3).
Proof. exact (SYM (@lem3784326 t1 t2 t3)). Qed.
Lemma lem3784328 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : term78 A f s.
Proof. exact (conj (@lem3781495 A s f h2) (@lem3781493 A s h1)). Qed.
Lemma lem3784329 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term13 A f) (h3 : term22 A s f) : term79 A f s.
Proof. exact (conj (@lem3781497 A f h2) (@lem3784328 A s f h1 h3)). Qed.
Lemma lem3784330 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term80 A f s.
Proof. exact (conj (@lem3781496 A f h1) (@lem3784329 A s f h2 h3 h4)). Qed.
Lemma lem3784331 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term13 A t) (h5 : term22 A s f) : term557 A t f s.
Proof. exact (conj (@lem3781483 A t h4) (@lem3784330 A s f h1 h2 h3 h5)). Qed.
Lemma lem3784332 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) : term558 A t f s.
Proof. exact (conj (@lem3784196 A t h3) (@lem3784331 A t s f h1 h2 h4 h5 h6)). Qed.
Lemma lem3784333 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : @SUBSET (A -> Prop) t f) : term559 A t f s.
Proof. exact (conj (@lem3784198 A t f h7) (@lem3784332 A t s f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem3784334 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term560 A t f s.
Proof. exact (conj (@lem3784197 A s t h7) (@lem3784333 A s t f h1 h2 h3 h4 h5 h6 h8)). Qed.
Lemma lem3784340 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784341 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784340 A s t). Qed.
Lemma lem3784342 {A : Type'} (s : A -> Prop) (t : type686 A) : (term22 A s t) = (term106 A s t).
Proof. exact (@lem3784341 A s (@UNIONS A t)). Qed.
Lemma lem3784349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784350 {A : Type'} (s : A -> Prop) (t : type686 A) : (term107 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3784349) (@lem3784342 A s t)). Qed.
Lemma lem3784354 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784355 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem3784354 (A -> Prop) s t). Qed.
Lemma lem3784356 {A : Type'} (t : type686 A) (f : type686 A) : (@SUBSET (A -> Prop) t f) = (term115 A t f).
Proof. exact (@lem3784355 A t f). Qed.
Lemma lem3784363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784364 {A : Type'} (t : type686 A) (f : type686 A) : (term68 A t f) = (term561 A t f).
Proof. exact (MK_COMB (@lem3784363) (@lem3784356 A t f)). Qed.
Lemma lem3784372 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3784373 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term83 A s t).
Proof. exact (@lem3784372 (A -> Prop) s t). Qed.
Lemma lem3784374 {A : Type'} (t : type686 A) : (t = (@EMPTY (A -> Prop))) = (term84 A t).
Proof. exact (@lem3784373 A t (@EMPTY (A -> Prop))). Qed.
Lemma lem3784383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784384 {A : Type'} (t : type686 A) : (term13 A t) = (term103 A t).
Proof. exact (MK_COMB (@lem3784383) (@lem3784374 A t)). Qed.
Lemma lem3784385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784386 {A : Type'} (t : type686 A) : (term104 A t) = (term105 A t).
Proof. exact (MK_COMB (@lem3784385) (@lem3784384 A t)). Qed.
Lemma lem3784404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784404 A s t). Qed.
Lemma lem3784406 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term10 A t u).
Proof. exact (@lem3784405 A t u). Qed.
Lemma lem3784413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3784414 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term87 A t u) = (term88 A t u).
Proof. exact (MK_COMB (@lem3784413) (@lem3784406 A t u)). Qed.
Lemma lem3784416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784416 A s t). Qed.
Lemma lem3784418 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (@SUBSET A u t) = (term10 A u t).
Proof. exact (@lem3784417 A u t). Qed.
Lemma lem3784425 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term89 A u t) = (term90 A u t).
Proof. exact (MK_COMB (@lem3784414 A t u) (@lem3784418 A u t)). Qed.
Lemma lem3784428 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) : (term91 A t u f) = (term91 A t u f).
Proof. exact (eq_refl (term91 A t u f)). Qed.
Lemma lem3784429 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term92 A f u t) = (term93 A f u t).
Proof. exact (MK_COMB (@lem3784428 A t u f) (@lem3784425 A u t)). Qed.
Lemma lem3784432 {A : Type'} (f : type686 A) (t : A -> Prop) : (term94 A f t) = (term95 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3784429 A f u t)). Qed.
Lemma lem3784433 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784434 {A : Type'} (f : type686 A) (t : A -> Prop) : (term96 A f t) = (term97 A f t).
Proof. exact (MK_COMB (@lem3784433 A) (@lem3784432 A f t)). Qed.
Lemma lem3784439 {A : Type'} (f : type686 A) : (term98 A f) = (term99 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3784434 A f t)). Qed.
Lemma lem3784440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784441 {A : Type'} (f : type686 A) : (term23 A f) = (term100 A f).
Proof. exact (MK_COMB (@lem3784440 A) (@lem3784439 A f)). Qed.
Lemma lem3784446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784447 {A : Type'} (f : type686 A) : (term101 A f) = (term102 A f).
Proof. exact (MK_COMB (@lem3784446) (@lem3784441 A f)). Qed.
Lemma lem3784453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3784454 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term83 A s t).
Proof. exact (@lem3784453 (A -> Prop) s t). Qed.
Lemma lem3784455 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term84 A f).
Proof. exact (@lem3784454 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3784464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784465 {A : Type'} (f : type686 A) : (term13 A f) = (term103 A f).
Proof. exact (MK_COMB (@lem3784464) (@lem3784455 A f)). Qed.
Lemma lem3784466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784467 {A : Type'} (f : type686 A) : (term104 A f) = (term105 A f).
Proof. exact (MK_COMB (@lem3784466) (@lem3784465 A f)). Qed.
Lemma lem3784471 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784472 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784471 A s t). Qed.
Lemma lem3784473 {A : Type'} (s : A -> Prop) (f : type686 A) : (term22 A s f) = (term106 A s f).
Proof. exact (@lem3784472 A s (@UNIONS A f)). Qed.
Lemma lem3784480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784481 {A : Type'} (s : A -> Prop) (f : type686 A) : (term107 A s f) = (term108 A s f).
Proof. exact (MK_COMB (@lem3784480) (@lem3784473 A s f)). Qed.
Lemma lem3784482 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3784483 {A : Type'} (f : type686 A) (s : A -> Prop) : (term78 A f s) = (term109 A f s).
Proof. exact (MK_COMB (@lem3784481 A s f) (@lem3784482 A s)). Qed.
Lemma lem3784486 {A : Type'} (f : type686 A) (s : A -> Prop) : (term79 A f s) = (term110 A f s).
Proof. exact (MK_COMB (@lem3784467 A f) (@lem3784483 A f s)). Qed.
Lemma lem3784489 {A : Type'} (f : type686 A) (s : A -> Prop) : (term80 A f s) = (term111 A f s).
Proof. exact (MK_COMB (@lem3784447 A f) (@lem3784486 A f s)). Qed.
Lemma lem3784492 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term557 A t f s) = (term562 A t f s).
Proof. exact (MK_COMB (@lem3784386 A t) (@lem3784489 A f s)). Qed.
Lemma lem3784495 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3784496 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term558 A t f s) = (term563 A t f s).
Proof. exact (MK_COMB (@lem3784495 A t) (@lem3784492 A t f s)). Qed.
Lemma lem3784499 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term559 A t f s) = (term564 A t f s).
Proof. exact (MK_COMB (@lem3784364 A t f) (@lem3784496 A t f s)). Qed.
Lemma lem3784502 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term560 A t f s) = (term565 A t f s).
Proof. exact (MK_COMB (@lem3784350 A s t) (@lem3784499 A t f s)). Qed.
Lemma lem3784505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784506 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term566 A t f s) = (term567 A t f s).
Proof. exact (MK_COMB (@lem3784505) (@lem3784502 A t f s)). Qed.
Lemma lem3784514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3784515 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term83 A s t).
Proof. exact (@lem3784514 (A -> Prop) s t). Qed.
Lemma lem3784516 {A : Type'} (t : type686 A) : (t = (@EMPTY (A -> Prop))) = (term84 A t).
Proof. exact (@lem3784515 A t (@EMPTY (A -> Prop))). Qed.
Lemma lem3784525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784526 {A : Type'} (t : type686 A) : (term13 A t) = (term103 A t).
Proof. exact (MK_COMB (@lem3784525) (@lem3784516 A t)). Qed.
Lemma lem3784527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784528 {A : Type'} (t : type686 A) : (term104 A t) = (term105 A t).
Proof. exact (MK_COMB (@lem3784527) (@lem3784526 A t)). Qed.
Lemma lem3784544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784545 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784544 A s t). Qed.
Lemma lem3784552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3784553 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term88 A s t).
Proof. exact (MK_COMB (@lem3784552) (@lem3784545 A s t)). Qed.
Lemma lem3784555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3784556 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem3784555 A s t). Qed.
Lemma lem3784557 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term10 A t s).
Proof. exact (@lem3784556 A t s). Qed.
Lemma lem3784564 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A t s) = (term90 A t s).
Proof. exact (MK_COMB (@lem3784553 A s t) (@lem3784557 A t s)). Qed.
Lemma lem3784567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (t' : type686 A) : (term91 A s t t') = (term91 A s t t').
Proof. exact (eq_refl (term91 A s t t')). Qed.
Lemma lem3784568 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term92 A t t' s) = (term93 A t t' s).
Proof. exact (MK_COMB (@lem3784567 A s t' t) (@lem3784564 A t' s)). Qed.
Lemma lem3784571 {A : Type'} (t : type686 A) (s : A -> Prop) : (term94 A t s) = (term95 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3784568 A t t' s)). Qed.
Lemma lem3784572 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784573 {A : Type'} (t : type686 A) (s : A -> Prop) : (term96 A t s) = (term97 A t s).
Proof. exact (MK_COMB (@lem3784572 A) (@lem3784571 A t s)). Qed.
Lemma lem3784578 {A : Type'} (t : type686 A) : (term98 A t) = (term99 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3784573 A t s)). Qed.
Lemma lem3784579 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784580 {A : Type'} (t : type686 A) : (term23 A t) = (term100 A t).
Proof. exact (MK_COMB (@lem3784579 A) (@lem3784578 A t)). Qed.
Lemma lem3784585 {A : Type'} (t : type686 A) : (term21 A t) = (term568 A t).
Proof. exact (MK_COMB (@lem3784528 A t) (@lem3784580 A t)). Qed.
Lemma lem3784588 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3784589 {A : Type'} (t : type686 A) : (term3 A t) = (term569 A t).
Proof. exact (MK_COMB (@lem3784588 A t) (@lem3784585 A t)). Qed.
Lemma lem3784592 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term570 A f s t) = (term571 A f s t).
Proof. exact (MK_COMB (@lem3784506 A t f s) (@lem3784589 A t)). Qed.
Lemma lem3784595 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term571 A f s t) = (term570 A f s t).
Proof. exact (SYM (@lem3784592 A f s t)). Qed.
Lemma lem3784607 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784608 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784607 A P x). Qed.
Lemma lem3784609 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3784608 A s x). Qed.
Lemma lem3784610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784611 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3784610) (@lem3784609 A s x)). Qed.
Lemma lem3784613 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3784614 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (@lem3784613 A s x). Qed.
Lemma lem3784615 {A : Type'} (t : type686 A) (x : A) : (term160 A x t) = (term161 A t x).
Proof. exact (@lem3784614 A t x). Qed.
Lemma lem3784623 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784624 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784623 (A -> Prop) P x). Qed.
Lemma lem3784625 {A : Type'} (t : type686 A) (t' : A -> Prop) : (@IN (A -> Prop) t' t) = (t t').
Proof. exact (@lem3784624 A t t'). Qed.
Lemma lem3784626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784627 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term123 A t' t) = (term139 A t t').
Proof. exact (MK_COMB (@lem3784626) (@lem3784625 A t t')). Qed.
Lemma lem3784629 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784630 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784629 A P x). Qed.
Lemma lem3784631 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3784630 A t x). Qed.
Lemma lem3784632 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term162 A t x t') = (term163 A t t' x).
Proof. exact (MK_COMB (@lem3784627 A t t') (@lem3784631 A t' x)). Qed.
Lemma lem3784635 {A : Type'} (t : type686 A) (x : A) : (term164 A t x) = (term165 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3784632 A t t' x)). Qed.
Lemma lem3784636 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3784637 {A : Type'} (t : type686 A) (x : A) : (term161 A t x) = (term166 A t x).
Proof. exact (MK_COMB (@lem3784636 A) (@lem3784635 A t x)). Qed.
Lemma lem3784642 {A : Type'} (t : type686 A) (x : A) : (term160 A x t) = (term166 A t x).
Proof. exact (TRANS (@lem3784615 A t x) (@lem3784637 A t x)). Qed.
Lemma lem3784643 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term167 A s x t) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3784611 A s x) (@lem3784642 A t x)). Qed.
Lemma lem3784646 {A : Type'} (s : A -> Prop) (t : type686 A) : (term169 A s t) = (term170 A s t).
Proof. exact (fun_ext (fun x : A => @lem3784643 A s t x)). Qed.
Lemma lem3784647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3784648 {A : Type'} (s : A -> Prop) (t : type686 A) : (term106 A s t) = (term171 A s t).
Proof. exact (MK_COMB (@lem3784647 A) (@lem3784646 A s t)). Qed.
Lemma lem3784653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784654 {A : Type'} (s : A -> Prop) (t : type686 A) : (term108 A s t) = (term172 A s t).
Proof. exact (MK_COMB (@lem3784653) (@lem3784648 A s t)). Qed.
Lemma lem3784664 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784665 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784664 (A -> Prop) P x). Qed.
Lemma lem3784666 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem3784665 A t x). Qed.
Lemma lem3784667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784668 {A : Type'} (t : type686 A) (x : A -> Prop) : (term572 A x t) = (term573 A t x).
Proof. exact (MK_COMB (@lem3784667) (@lem3784666 A t x)). Qed.
Lemma lem3784670 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784671 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784670 (A -> Prop) P x). Qed.
Lemma lem3784672 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3784671 A f x). Qed.
Lemma lem3784673 {A : Type'} (t : type686 A) (f : type686 A) (x : A -> Prop) : (term546 A t x f) = (term574 A t f x).
Proof. exact (MK_COMB (@lem3784668 A t x) (@lem3784672 A f x)). Qed.
Lemma lem3784676 {A : Type'} (t : type686 A) (f : type686 A) : (term575 A t f) = (term576 A t f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3784673 A t f x)). Qed.
Lemma lem3784677 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784678 {A : Type'} (t : type686 A) (f : type686 A) : (term115 A t f) = (term577 A t f).
Proof. exact (MK_COMB (@lem3784677 A) (@lem3784676 A t f)). Qed.
Lemma lem3784683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784684 {A : Type'} (t : type686 A) (f : type686 A) : (term561 A t f) = (term578 A t f).
Proof. exact (MK_COMB (@lem3784683) (@lem3784678 A t f)). Qed.
Lemma lem3784696 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784697 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784696 (A -> Prop) P x). Qed.
Lemma lem3784698 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem3784697 A t x). Qed.
Lemma lem3784699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3784700 {A : Type'} (t : type686 A) (x : A -> Prop) : (term132 A x t) = (term133 A t x).
Proof. exact (MK_COMB (@lem3784699) (@lem3784698 A t x)). Qed.
Lemma lem3784702 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3784703 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3784702 (A -> Prop) x). Qed.
Lemma lem3784704 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem3784700 A t x) (@lem3784703 A x)). Qed.
Lemma lem3784706 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3784707 {A : Type'} (t : type686 A) (x : A -> Prop) : ((t x) = False) = (term134 A t x).
Proof. exact (@lem3784706 (t x)). Qed.
Lemma lem3784708 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term134 A t x).
Proof. exact (TRANS (@lem3784704 A t x) (@lem3784707 A t x)). Qed.
Lemma lem3784709 {A : Type'} (t : type686 A) : (term135 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3784708 A t x)). Qed.
Lemma lem3784710 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784711 {A : Type'} (t : type686 A) : (term84 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3784710 A) (@lem3784709 A t)). Qed.
Lemma lem3784716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784717 {A : Type'} (t : type686 A) : (term103 A t) = (term158 A t).
Proof. exact (MK_COMB (@lem3784716) (@lem3784711 A t)). Qed.
Lemma lem3784718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784719 {A : Type'} (t : type686 A) : (term105 A t) = (term159 A t).
Proof. exact (MK_COMB (@lem3784718) (@lem3784717 A t)). Qed.
Lemma lem3784735 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784736 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784735 (A -> Prop) P x). Qed.
Lemma lem3784737 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3784736 A f t). Qed.
Lemma lem3784738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784739 {A : Type'} (f : type686 A) (t : A -> Prop) : (term123 A t f) = (term139 A f t).
Proof. exact (MK_COMB (@lem3784738) (@lem3784737 A f t)). Qed.
Lemma lem3784741 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784742 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784741 (A -> Prop) P x). Qed.
Lemma lem3784743 {A : Type'} (f : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u f) = (f u).
Proof. exact (@lem3784742 A f u). Qed.
Lemma lem3784744 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term140 A t u f) = (term141 A t f u).
Proof. exact (MK_COMB (@lem3784739 A f t) (@lem3784743 A f u)). Qed.
Lemma lem3784747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784748 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term91 A t u f) = (term142 A t f u).
Proof. exact (MK_COMB (@lem3784747) (@lem3784744 A t f u)). Qed.
Lemma lem3784758 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784759 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784758 A P x). Qed.
Lemma lem3784760 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3784759 A t x). Qed.
Lemma lem3784761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784762 {A : Type'} (t : A -> Prop) (x : A) : (term143 A x t) = (term144 A t x).
Proof. exact (MK_COMB (@lem3784761) (@lem3784760 A t x)). Qed.
Lemma lem3784764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784765 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784764 A P x). Qed.
Lemma lem3784766 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3784765 A u x). Qed.
Lemma lem3784767 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term145 A t x u) = (term146 A t u x).
Proof. exact (MK_COMB (@lem3784762 A t x) (@lem3784766 A u x)). Qed.
Lemma lem3784770 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term147 A t u) = (term148 A t u).
Proof. exact (fun_ext (fun x : A => @lem3784767 A t u x)). Qed.
Lemma lem3784771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3784772 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term10 A t u) = (term149 A t u).
Proof. exact (MK_COMB (@lem3784771 A) (@lem3784770 A t u)). Qed.
Lemma lem3784777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3784778 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term88 A t u) = (term150 A t u).
Proof. exact (MK_COMB (@lem3784777) (@lem3784772 A t u)). Qed.
Lemma lem3784786 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784787 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784786 A P x). Qed.
Lemma lem3784788 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3784787 A u x). Qed.
Lemma lem3784789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784790 {A : Type'} (u : A -> Prop) (x : A) : (term143 A x u) = (term144 A u x).
Proof. exact (MK_COMB (@lem3784789) (@lem3784788 A u x)). Qed.
Lemma lem3784792 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784793 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784792 A P x). Qed.
Lemma lem3784794 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3784793 A t x). Qed.
Lemma lem3784795 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term145 A u x t) = (term146 A u t x).
Proof. exact (MK_COMB (@lem3784790 A u x) (@lem3784794 A t x)). Qed.
Lemma lem3784798 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term147 A u t) = (term148 A u t).
Proof. exact (fun_ext (fun x : A => @lem3784795 A u t x)). Qed.
Lemma lem3784799 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3784800 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term10 A u t) = (term149 A u t).
Proof. exact (MK_COMB (@lem3784799 A) (@lem3784798 A u t)). Qed.
Lemma lem3784805 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term90 A u t) = (term151 A u t).
Proof. exact (MK_COMB (@lem3784778 A t u) (@lem3784800 A u t)). Qed.
Lemma lem3784808 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term93 A f u t) = (term152 A f u t).
Proof. exact (MK_COMB (@lem3784748 A t f u) (@lem3784805 A u t)). Qed.
Lemma lem3784811 {A : Type'} (f : type686 A) (t : A -> Prop) : (term95 A f t) = (term153 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3784808 A f u t)). Qed.
Lemma lem3784812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784813 {A : Type'} (f : type686 A) (t : A -> Prop) : (term97 A f t) = (term154 A f t).
Proof. exact (MK_COMB (@lem3784812 A) (@lem3784811 A f t)). Qed.
Lemma lem3784818 {A : Type'} (f : type686 A) : (term99 A f) = (term155 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3784813 A f t)). Qed.
Lemma lem3784819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784820 {A : Type'} (f : type686 A) : (term100 A f) = (term156 A f).
Proof. exact (MK_COMB (@lem3784819 A) (@lem3784818 A f)). Qed.
Lemma lem3784825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784826 {A : Type'} (f : type686 A) : (term102 A f) = (term157 A f).
Proof. exact (MK_COMB (@lem3784825) (@lem3784820 A f)). Qed.
Lemma lem3784836 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784837 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784836 (A -> Prop) P x). Qed.
Lemma lem3784838 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3784837 A f x). Qed.
Lemma lem3784839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3784840 {A : Type'} (f : type686 A) (x : A -> Prop) : (term132 A x f) = (term133 A f x).
Proof. exact (MK_COMB (@lem3784839) (@lem3784838 A f x)). Qed.
Lemma lem3784842 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3784843 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3784842 (A -> Prop) x). Qed.
Lemma lem3784844 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3784840 A f x) (@lem3784843 A x)). Qed.
Lemma lem3784846 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3784847 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term134 A f x).
Proof. exact (@lem3784846 (f x)). Qed.
Lemma lem3784848 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term134 A f x).
Proof. exact (TRANS (@lem3784844 A f x) (@lem3784847 A f x)). Qed.
Lemma lem3784849 {A : Type'} (f : type686 A) : (term135 A f) = (term136 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3784848 A f x)). Qed.
Lemma lem3784850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784851 {A : Type'} (f : type686 A) : (term84 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3784850 A) (@lem3784849 A f)). Qed.
Lemma lem3784856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784857 {A : Type'} (f : type686 A) : (term103 A f) = (term158 A f).
Proof. exact (MK_COMB (@lem3784856) (@lem3784851 A f)). Qed.
Lemma lem3784858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784859 {A : Type'} (f : type686 A) : (term105 A f) = (term159 A f).
Proof. exact (MK_COMB (@lem3784858) (@lem3784857 A f)). Qed.
Lemma lem3784869 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784870 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784869 A P x). Qed.
Lemma lem3784871 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3784870 A s x). Qed.
Lemma lem3784872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784873 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3784872) (@lem3784871 A s x)). Qed.
Lemma lem3784875 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3784876 {A : Type'} (s : type686 A) (x : A) : (term160 A x s) = (term161 A s x).
Proof. exact (@lem3784875 A s x). Qed.
Lemma lem3784877 {A : Type'} (f : type686 A) (x : A) : (term160 A x f) = (term161 A f x).
Proof. exact (@lem3784876 A f x). Qed.
Lemma lem3784885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784886 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784885 (A -> Prop) P x). Qed.
Lemma lem3784887 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3784886 A f t). Qed.
Lemma lem3784888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784889 {A : Type'} (f : type686 A) (t : A -> Prop) : (term123 A t f) = (term139 A f t).
Proof. exact (MK_COMB (@lem3784888) (@lem3784887 A f t)). Qed.
Lemma lem3784891 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784892 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3784891 A P x). Qed.
Lemma lem3784893 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3784892 A t x). Qed.
Lemma lem3784894 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term162 A f x t) = (term163 A f t x).
Proof. exact (MK_COMB (@lem3784889 A f t) (@lem3784893 A t x)). Qed.
Lemma lem3784897 {A : Type'} (f : type686 A) (x : A) : (term164 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3784894 A f t x)). Qed.
Lemma lem3784898 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3784899 {A : Type'} (f : type686 A) (x : A) : (term161 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3784898 A) (@lem3784897 A f x)). Qed.
Lemma lem3784904 {A : Type'} (f : type686 A) (x : A) : (term160 A x f) = (term166 A f x).
Proof. exact (TRANS (@lem3784877 A f x) (@lem3784899 A f x)). Qed.
Lemma lem3784905 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term167 A s x f) = (term168 A s f x).
Proof. exact (MK_COMB (@lem3784873 A s x) (@lem3784904 A f x)). Qed.
Lemma lem3784908 {A : Type'} (s : A -> Prop) (f : type686 A) : (term169 A s f) = (term170 A s f).
Proof. exact (fun_ext (fun x : A => @lem3784905 A s f x)). Qed.
Lemma lem3784909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3784910 {A : Type'} (s : A -> Prop) (f : type686 A) : (term106 A s f) = (term171 A s f).
Proof. exact (MK_COMB (@lem3784909 A) (@lem3784908 A s f)). Qed.
Lemma lem3784915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784916 {A : Type'} (s : A -> Prop) (f : type686 A) : (term108 A s f) = (term172 A s f).
Proof. exact (MK_COMB (@lem3784915) (@lem3784910 A s f)). Qed.
Lemma lem3784917 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3784918 {A : Type'} (f : type686 A) (s : A -> Prop) : (term109 A f s) = (term173 A f s).
Proof. exact (MK_COMB (@lem3784916 A s f) (@lem3784917 A s)). Qed.
Lemma lem3784921 {A : Type'} (f : type686 A) (s : A -> Prop) : (term110 A f s) = (term174 A f s).
Proof. exact (MK_COMB (@lem3784859 A f) (@lem3784918 A f s)). Qed.
Lemma lem3784924 {A : Type'} (f : type686 A) (s : A -> Prop) : (term111 A f s) = (term175 A f s).
Proof. exact (MK_COMB (@lem3784826 A f) (@lem3784921 A f s)). Qed.
Lemma lem3784927 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term562 A t f s) = (term579 A t f s).
Proof. exact (MK_COMB (@lem3784719 A t) (@lem3784924 A f s)). Qed.
Lemma lem3784930 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3784931 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term563 A t f s) = (term580 A t f s).
Proof. exact (MK_COMB (@lem3784930 A t) (@lem3784927 A t f s)). Qed.
Lemma lem3784934 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term564 A t f s) = (term581 A t f s).
Proof. exact (MK_COMB (@lem3784684 A t f) (@lem3784931 A t f s)). Qed.
Lemma lem3784937 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term565 A t f s) = (term582 A t f s).
Proof. exact (MK_COMB (@lem3784654 A s t) (@lem3784934 A t f s)). Qed.
Lemma lem3784940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3784941 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term567 A t f s) = (term583 A t f s).
Proof. exact (MK_COMB (@lem3784940) (@lem3784937 A t f s)). Qed.
Lemma lem3784953 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784954 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784953 (A -> Prop) P x). Qed.
Lemma lem3784955 {A : Type'} (t : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x t) = (t x).
Proof. exact (@lem3784954 A t x). Qed.
Lemma lem3784956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3784957 {A : Type'} (t : type686 A) (x : A -> Prop) : (term132 A x t) = (term133 A t x).
Proof. exact (MK_COMB (@lem3784956) (@lem3784955 A t x)). Qed.
Lemma lem3784959 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3784960 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3784959 (A -> Prop) x). Qed.
Lemma lem3784961 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem3784957 A t x) (@lem3784960 A x)). Qed.
Lemma lem3784963 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3784964 {A : Type'} (t : type686 A) (x : A -> Prop) : ((t x) = False) = (term134 A t x).
Proof. exact (@lem3784963 (t x)). Qed.
Lemma lem3784965 {A : Type'} (t : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x t) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term134 A t x).
Proof. exact (TRANS (@lem3784961 A t x) (@lem3784964 A t x)). Qed.
Lemma lem3784966 {A : Type'} (t : type686 A) : (term135 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3784965 A t x)). Qed.
Lemma lem3784967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3784968 {A : Type'} (t : type686 A) : (term84 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3784967 A) (@lem3784966 A t)). Qed.
Lemma lem3784973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3784974 {A : Type'} (t : type686 A) : (term103 A t) = (term158 A t).
Proof. exact (MK_COMB (@lem3784973) (@lem3784968 A t)). Qed.
Lemma lem3784975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784976 {A : Type'} (t : type686 A) : (term105 A t) = (term159 A t).
Proof. exact (MK_COMB (@lem3784975) (@lem3784974 A t)). Qed.
Lemma lem3784990 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784991 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784990 (A -> Prop) P x). Qed.
Lemma lem3784992 {A : Type'} (t : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s t) = (t s).
Proof. exact (@lem3784991 A t s). Qed.
Lemma lem3784993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3784994 {A : Type'} (t : type686 A) (s : A -> Prop) : (term123 A s t) = (term139 A t s).
Proof. exact (MK_COMB (@lem3784993) (@lem3784992 A t s)). Qed.
Lemma lem3784996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3784997 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3784996 (A -> Prop) P x). Qed.
Lemma lem3784998 {A : Type'} (t : type686 A) (t' : A -> Prop) : (@IN (A -> Prop) t' t) = (t t').
Proof. exact (@lem3784997 A t t'). Qed.
Lemma lem3784999 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term140 A s t' t) = (term141 A s t t').
Proof. exact (MK_COMB (@lem3784994 A t s) (@lem3784998 A t t')). Qed.
Lemma lem3785002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3785003 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term91 A s t' t) = (term142 A s t t').
Proof. exact (MK_COMB (@lem3785002) (@lem3784999 A s t t')). Qed.
Lemma lem3785013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3785014 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3785013 A P x). Qed.
Lemma lem3785015 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3785014 A s x). Qed.
Lemma lem3785016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3785017 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3785016) (@lem3785015 A s x)). Qed.
Lemma lem3785019 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3785020 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3785019 A P x). Qed.
Lemma lem3785021 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3785020 A t x). Qed.
Lemma lem3785022 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term145 A s x t) = (term146 A s t x).
Proof. exact (MK_COMB (@lem3785017 A s x) (@lem3785021 A t x)). Qed.
Lemma lem3785025 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term148 A s t).
Proof. exact (fun_ext (fun x : A => @lem3785022 A s t x)). Qed.
Lemma lem3785026 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785027 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3785026 A) (@lem3785025 A s t)). Qed.
Lemma lem3785032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3785033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term150 A s t).
Proof. exact (MK_COMB (@lem3785032) (@lem3785027 A s t)). Qed.
Lemma lem3785041 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3785042 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3785041 A P x). Qed.
Lemma lem3785043 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3785042 A t x). Qed.
Lemma lem3785044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3785045 {A : Type'} (t : A -> Prop) (x : A) : (term143 A x t) = (term144 A t x).
Proof. exact (MK_COMB (@lem3785044) (@lem3785043 A t x)). Qed.
Lemma lem3785047 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3785048 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3785047 A P x). Qed.
Lemma lem3785049 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3785048 A s x). Qed.
Lemma lem3785050 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term145 A t x s) = (term146 A t s x).
Proof. exact (MK_COMB (@lem3785045 A t x) (@lem3785049 A s x)). Qed.
Lemma lem3785053 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term147 A t s) = (term148 A t s).
Proof. exact (fun_ext (fun x : A => @lem3785050 A t s x)). Qed.
Lemma lem3785054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785055 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term10 A t s) = (term149 A t s).
Proof. exact (MK_COMB (@lem3785054 A) (@lem3785053 A t s)). Qed.
Lemma lem3785060 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term90 A t s) = (term151 A t s).
Proof. exact (MK_COMB (@lem3785033 A s t) (@lem3785055 A t s)). Qed.
Lemma lem3785063 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term93 A t t' s) = (term152 A t t' s).
Proof. exact (MK_COMB (@lem3785003 A s t t') (@lem3785060 A t' s)). Qed.
Lemma lem3785066 {A : Type'} (t : type686 A) (s : A -> Prop) : (term95 A t s) = (term153 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3785063 A t t' s)). Qed.
Lemma lem3785067 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785068 {A : Type'} (t : type686 A) (s : A -> Prop) : (term97 A t s) = (term154 A t s).
Proof. exact (MK_COMB (@lem3785067 A) (@lem3785066 A t s)). Qed.
Lemma lem3785073 {A : Type'} (t : type686 A) : (term99 A t) = (term155 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3785068 A t s)). Qed.
Lemma lem3785074 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785075 {A : Type'} (t : type686 A) : (term100 A t) = (term156 A t).
Proof. exact (MK_COMB (@lem3785074 A) (@lem3785073 A t)). Qed.
Lemma lem3785080 {A : Type'} (t : type686 A) : (term568 A t) = (term584 A t).
Proof. exact (MK_COMB (@lem3784976 A t) (@lem3785075 A t)). Qed.
Lemma lem3785083 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3785084 {A : Type'} (t : type686 A) : (term569 A t) = (term585 A t).
Proof. exact (MK_COMB (@lem3785083 A t) (@lem3785080 A t)). Qed.
Lemma lem3785087 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term571 A f s t) = (term586 A f s t).
Proof. exact (MK_COMB (@lem3784941 A t f s) (@lem3785084 A t)). Qed.
Lemma lem3785090 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term586 A f s t) = (term571 A f s t).
Proof. exact (SYM (@lem3785087 A f s t)). Qed.
Lemma lem3785092 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3785093 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term586 A f s t) = (term587 A f s t).
Proof. exact (@lem3785092 (term586 A f s t)). Qed.
Lemma lem3785094 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term587 A f s t) = (term586 A f s t).
Proof. exact (SYM (@lem3785093 A f s t)). Qed.
Lemma lem3785095 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term588 A f s t) : term588 A f s t.
Proof. exact (h1). Qed.
Lemma lem3785098 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term587 A f s t) : term587 A f s t.
Proof. exact (h1). Qed.
Lemma lem3785099 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term589 A f s t.
Proof. exact (fun h0 : term587 A f s t => @lem3785098 A f s t h0). Qed.
Lemma lem3785100 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term589 A f s t) : term589 A f s t.
Proof. exact (h1). Qed.
Lemma lem3785101 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term587 A f s t) : term587 A f s t.
Proof. exact (h1). Qed.
Lemma lem3785102 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term587 A f s t) (h2 : term589 A f s t) : term587 A f s t.
Proof. exact (@lem3785100 A f s t h2 (@lem3785101 A f s t h1)). Qed.
Lemma lem3785103 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term587 A f s t) : term590 A f s t.
Proof. exact (fun h0 : term589 A f s t => @lem3785102 A f s t h1 h0). Qed.
Lemma lem3785104 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term589 A f s t) : term589 A f s t.
Proof. exact (h1). Qed.
Lemma lem3785105 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term587 A f s t) (h2 : term589 A f s t) : term587 A f s t.
Proof. exact (@lem3785103 A f s t h1 (@lem3785104 A f s t h2)). Qed.
Lemma lem3785106 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term589 A f s t) : term589 A f s t.
Proof. exact (fun h0 : term587 A f s t => @lem3785105 A f s t h0 h1). Qed.
Lemma lem3785107 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term591 A f s t.
Proof. exact (fun h0 : term589 A f s t => @lem3785106 A f s t h0). Qed.
Lemma lem3785110 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term589 A f s t.
Proof. exact (@lem3785107 A f s t (@lem3785099 A f s t)). Qed.
Lemma lem3785111 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term589 A f s t.
Proof. exact (@lem3785110 A f s t). Qed.
Lemma lem3785125 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3785126 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term587 A f s t) = (term592 A f s t).
Proof. exact (@lem3785125 (term588 A f s t)). Qed.
Lemma lem3785128 (t : Prop) : (term207 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3785129 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term592 A f s t) = (term586 A f s t).
Proof. exact (@lem3785128 (term586 A f s t)). Qed.
Lemma lem3785132 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term587 A f s t) = (term586 A f s t).
Proof. exact (TRANS (@lem3785126 A f s t) (@lem3785129 A f s t)). Qed.
Lemma lem3785293 {A : Type'} (s : A -> Prop) (t : type686 A) : (term593 A s t) = (term594 A s t).
Proof. exact (fun_ext (fun f : type686 A => @lem3785132 A f s t)). Qed.
Lemma lem3785294 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3785295 {A : Type'} (s : A -> Prop) (t : type686 A) : (term595 A s t) = (term596 A s t).
Proof. exact (MK_COMB (@lem3785294 A) (@lem3785293 A s t)). Qed.
Lemma lem3785300 {A : Type'} (t : type686 A) : (term597 A t) = (term598 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3785295 A s t)). Qed.
Lemma lem3785301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785302 {A : Type'} (t : type686 A) : (term599 A t) = (term600 A t).
Proof. exact (MK_COMB (@lem3785301 A) (@lem3785300 A t)). Qed.
Lemma lem3785307 {A : Type'} : (term601 A) = (term602 A).
Proof. exact (fun_ext (fun t : type686 A => @lem3785302 A t)). Qed.
Lemma lem3785308 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3785317 {A : Type'} : (term603 A) = (term604 A).
Proof. exact (MK_COMB (@lem3785308 A) (@lem3785307 A)). Qed.
Lemma lem3785322 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term146 A t s x) = (term146 A t s x).
Proof. exact (eq_refl (term146 A t s x)). Qed.
Lemma lem3785323 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term148 A t s) = (term148 A t s).
Proof. exact (fun_ext (fun x : A => @lem3785322 A t s x)). Qed.
Lemma lem3785324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785325 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term149 A t s) = (term149 A t s).
Proof. exact (MK_COMB (@lem3785324 A) (@lem3785323 A t s)). Qed.
Lemma lem3785330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A s t x) = (term146 A s t x).
Proof. exact (eq_refl (term146 A s t x)). Qed.
Lemma lem3785331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term148 A s t) = (term148 A s t).
Proof. exact (fun_ext (fun x : A => @lem3785330 A s t x)). Qed.
Lemma lem3785332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785333 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3785332 A) (@lem3785331 A s t)). Qed.
Lemma lem3785334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3785335 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term150 A s t).
Proof. exact (MK_COMB (@lem3785334) (@lem3785333 A s t)). Qed.
Lemma lem3785336 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term151 A t s) = (term151 A t s).
Proof. exact (MK_COMB (@lem3785335 A s t) (@lem3785325 A t s)). Qed.
Lemma lem3785343 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term142 A s t t') = (term142 A s t t').
Proof. exact (eq_refl (term142 A s t t')). Qed.
Lemma lem3785344 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term152 A t t' s) = (term152 A t t' s).
Proof. exact (MK_COMB (@lem3785343 A s t t') (@lem3785336 A t' s)). Qed.
Lemma lem3785345 {A : Type'} (t : type686 A) (s : A -> Prop) : (term153 A t s) = (term153 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3785344 A t t' s)). Qed.
Lemma lem3785346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785347 {A : Type'} (t : type686 A) (s : A -> Prop) : (term154 A t s) = (term154 A t s).
Proof. exact (MK_COMB (@lem3785346 A) (@lem3785345 A t s)). Qed.
Lemma lem3785348 {A : Type'} (t : type686 A) : (term155 A t) = (term155 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3785347 A t s)). Qed.
Lemma lem3785349 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785350 {A : Type'} (t : type686 A) : (term156 A t) = (term156 A t).
Proof. exact (MK_COMB (@lem3785349 A) (@lem3785348 A t)). Qed.
Lemma lem3785353 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term134 A t x).
Proof. exact (eq_refl (term134 A t x)). Qed.
Lemma lem3785354 {A : Type'} (t : type686 A) : (term136 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785353 A t x)). Qed.
Lemma lem3785355 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785356 {A : Type'} (t : type686 A) : (term137 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3785355 A) (@lem3785354 A t)). Qed.
Lemma lem3785357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3785358 {A : Type'} (t : type686 A) : (term158 A t) = (term158 A t).
Proof. exact (MK_COMB (@lem3785357) (@lem3785356 A t)). Qed.
Lemma lem3785359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785360 {A : Type'} (t : type686 A) : (term159 A t) = (term159 A t).
Proof. exact (MK_COMB (@lem3785359) (@lem3785358 A t)). Qed.
Lemma lem3785361 {A : Type'} (t : type686 A) : (term584 A t) = (term584 A t).
Proof. exact (MK_COMB (@lem3785360 A t) (@lem3785350 A t)). Qed.
Lemma lem3785364 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3785365 {A : Type'} (t : type686 A) : (term585 A t) = (term585 A t).
Proof. exact (MK_COMB (@lem3785364 A t) (@lem3785361 A t)). Qed.
Lemma lem3785366 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3785371 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term163 A f t x) = (term163 A f t x).
Proof. exact (eq_refl (term163 A f t x)). Qed.
Lemma lem3785372 {A : Type'} (f : type686 A) (x : A) : (term165 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3785371 A f t x)). Qed.
Lemma lem3785373 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785374 {A : Type'} (f : type686 A) (x : A) : (term166 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3785373 A) (@lem3785372 A f x)). Qed.
Lemma lem3785377 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term144 A s x).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem3785378 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term168 A s f x).
Proof. exact (MK_COMB (@lem3785377 A s x) (@lem3785374 A f x)). Qed.
Lemma lem3785379 {A : Type'} (s : A -> Prop) (f : type686 A) : (term170 A s f) = (term170 A s f).
Proof. exact (fun_ext (fun x : A => @lem3785378 A s f x)). Qed.
Lemma lem3785380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785381 {A : Type'} (s : A -> Prop) (f : type686 A) : (term171 A s f) = (term171 A s f).
Proof. exact (MK_COMB (@lem3785380 A) (@lem3785379 A s f)). Qed.
Lemma lem3785382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785383 {A : Type'} (s : A -> Prop) (f : type686 A) : (term172 A s f) = (term172 A s f).
Proof. exact (MK_COMB (@lem3785382) (@lem3785381 A s f)). Qed.
Lemma lem3785384 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term173 A f s).
Proof. exact (MK_COMB (@lem3785383 A s f) (@lem3785366 A s)). Qed.
Lemma lem3785387 {A : Type'} (f : type686 A) (x : A -> Prop) : (term134 A f x) = (term134 A f x).
Proof. exact (eq_refl (term134 A f x)). Qed.
Lemma lem3785388 {A : Type'} (f : type686 A) : (term136 A f) = (term136 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785387 A f x)). Qed.
Lemma lem3785389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785390 {A : Type'} (f : type686 A) : (term137 A f) = (term137 A f).
Proof. exact (MK_COMB (@lem3785389 A) (@lem3785388 A f)). Qed.
Lemma lem3785391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3785392 {A : Type'} (f : type686 A) : (term158 A f) = (term158 A f).
Proof. exact (MK_COMB (@lem3785391) (@lem3785390 A f)). Qed.
Lemma lem3785393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785394 {A : Type'} (f : type686 A) : (term159 A f) = (term159 A f).
Proof. exact (MK_COMB (@lem3785393) (@lem3785392 A f)). Qed.
Lemma lem3785395 {A : Type'} (f : type686 A) (s : A -> Prop) : (term174 A f s) = (term174 A f s).
Proof. exact (MK_COMB (@lem3785394 A f) (@lem3785384 A f s)). Qed.
Lemma lem3785400 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term146 A u t x) = (term146 A u t x).
Proof. exact (eq_refl (term146 A u t x)). Qed.
Lemma lem3785401 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term148 A u t) = (term148 A u t).
Proof. exact (fun_ext (fun x : A => @lem3785400 A u t x)). Qed.
Lemma lem3785402 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785403 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term149 A u t) = (term149 A u t).
Proof. exact (MK_COMB (@lem3785402 A) (@lem3785401 A u t)). Qed.
Lemma lem3785408 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term146 A t u x) = (term146 A t u x).
Proof. exact (eq_refl (term146 A t u x)). Qed.
Lemma lem3785409 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term148 A t u) = (term148 A t u).
Proof. exact (fun_ext (fun x : A => @lem3785408 A t u x)). Qed.
Lemma lem3785410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785411 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term149 A t u) = (term149 A t u).
Proof. exact (MK_COMB (@lem3785410 A) (@lem3785409 A t u)). Qed.
Lemma lem3785412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3785413 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term150 A t u) = (term150 A t u).
Proof. exact (MK_COMB (@lem3785412) (@lem3785411 A t u)). Qed.
Lemma lem3785414 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term151 A u t) = (term151 A u t).
Proof. exact (MK_COMB (@lem3785413 A t u) (@lem3785403 A u t)). Qed.
Lemma lem3785421 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term142 A t f u) = (term142 A t f u).
Proof. exact (eq_refl (term142 A t f u)). Qed.
Lemma lem3785422 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term152 A f u t).
Proof. exact (MK_COMB (@lem3785421 A t f u) (@lem3785414 A u t)). Qed.
Lemma lem3785423 {A : Type'} (f : type686 A) (t : A -> Prop) : (term153 A f t) = (term153 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3785422 A f u t)). Qed.
Lemma lem3785424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785425 {A : Type'} (f : type686 A) (t : A -> Prop) : (term154 A f t) = (term154 A f t).
Proof. exact (MK_COMB (@lem3785424 A) (@lem3785423 A f t)). Qed.
Lemma lem3785426 {A : Type'} (f : type686 A) : (term155 A f) = (term155 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3785425 A f t)). Qed.
Lemma lem3785427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785428 {A : Type'} (f : type686 A) : (term156 A f) = (term156 A f).
Proof. exact (MK_COMB (@lem3785427 A) (@lem3785426 A f)). Qed.
Lemma lem3785429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785430 {A : Type'} (f : type686 A) : (term157 A f) = (term157 A f).
Proof. exact (MK_COMB (@lem3785429) (@lem3785428 A f)). Qed.
Lemma lem3785431 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term175 A f s).
Proof. exact (MK_COMB (@lem3785430 A f) (@lem3785395 A f s)). Qed.
Lemma lem3785434 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term134 A t x).
Proof. exact (eq_refl (term134 A t x)). Qed.
Lemma lem3785435 {A : Type'} (t : type686 A) : (term136 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785434 A t x)). Qed.
Lemma lem3785436 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785437 {A : Type'} (t : type686 A) : (term137 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3785436 A) (@lem3785435 A t)). Qed.
Lemma lem3785438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3785439 {A : Type'} (t : type686 A) : (term158 A t) = (term158 A t).
Proof. exact (MK_COMB (@lem3785438) (@lem3785437 A t)). Qed.
Lemma lem3785440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785441 {A : Type'} (t : type686 A) : (term159 A t) = (term159 A t).
Proof. exact (MK_COMB (@lem3785440) (@lem3785439 A t)). Qed.
Lemma lem3785442 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term579 A t f s) = (term579 A t f s).
Proof. exact (MK_COMB (@lem3785441 A t) (@lem3785431 A f s)). Qed.
Lemma lem3785445 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3785446 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term580 A t f s) = (term580 A t f s).
Proof. exact (MK_COMB (@lem3785445 A t) (@lem3785442 A t f s)). Qed.
Lemma lem3785451 {A : Type'} (t : type686 A) (f : type686 A) (x : A -> Prop) : (term574 A t f x) = (term574 A t f x).
Proof. exact (eq_refl (term574 A t f x)). Qed.
Lemma lem3785452 {A : Type'} (t : type686 A) (f : type686 A) : (term576 A t f) = (term576 A t f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785451 A t f x)). Qed.
Lemma lem3785453 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785454 {A : Type'} (t : type686 A) (f : type686 A) : (term577 A t f) = (term577 A t f).
Proof. exact (MK_COMB (@lem3785453 A) (@lem3785452 A t f)). Qed.
Lemma lem3785455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785456 {A : Type'} (t : type686 A) (f : type686 A) : (term578 A t f) = (term578 A t f).
Proof. exact (MK_COMB (@lem3785455) (@lem3785454 A t f)). Qed.
Lemma lem3785457 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term581 A t f s) = (term581 A t f s).
Proof. exact (MK_COMB (@lem3785456 A t f) (@lem3785446 A t f s)). Qed.
Lemma lem3785462 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term163 A t t' x) = (term163 A t t' x).
Proof. exact (eq_refl (term163 A t t' x)). Qed.
Lemma lem3785463 {A : Type'} (t : type686 A) (x : A) : (term165 A t x) = (term165 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3785462 A t t' x)). Qed.
Lemma lem3785464 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785465 {A : Type'} (t : type686 A) (x : A) : (term166 A t x) = (term166 A t x).
Proof. exact (MK_COMB (@lem3785464 A) (@lem3785463 A t x)). Qed.
Lemma lem3785468 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term144 A s x).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem3785469 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term168 A s t x) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3785468 A s x) (@lem3785465 A t x)). Qed.
Lemma lem3785470 {A : Type'} (s : A -> Prop) (t : type686 A) : (term170 A s t) = (term170 A s t).
Proof. exact (fun_ext (fun x : A => @lem3785469 A s t x)). Qed.
Lemma lem3785471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785472 {A : Type'} (s : A -> Prop) (t : type686 A) : (term171 A s t) = (term171 A s t).
Proof. exact (MK_COMB (@lem3785471 A) (@lem3785470 A s t)). Qed.
Lemma lem3785473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785474 {A : Type'} (s : A -> Prop) (t : type686 A) : (term172 A s t) = (term172 A s t).
Proof. exact (MK_COMB (@lem3785473) (@lem3785472 A s t)). Qed.
Lemma lem3785475 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term582 A t f s) = (term582 A t f s).
Proof. exact (MK_COMB (@lem3785474 A s t) (@lem3785457 A t f s)). Qed.
Lemma lem3785476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3785477 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term583 A t f s) = (term583 A t f s).
Proof. exact (MK_COMB (@lem3785476) (@lem3785475 A t f s)). Qed.
Lemma lem3785478 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term586 A f s t) = (term586 A f s t).
Proof. exact (MK_COMB (@lem3785477 A t f s) (@lem3785365 A t)). Qed.
Lemma lem3785479 {A : Type'} (s : A -> Prop) (t : type686 A) : (term594 A s t) = (term594 A s t).
Proof. exact (fun_ext (fun f : type686 A => @lem3785478 A f s t)). Qed.
Lemma lem3785480 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3785481 {A : Type'} (s : A -> Prop) (t : type686 A) : (term596 A s t) = (term596 A s t).
Proof. exact (MK_COMB (@lem3785480 A) (@lem3785479 A s t)). Qed.
Lemma lem3785482 {A : Type'} (t : type686 A) : (term598 A t) = (term598 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3785481 A s t)). Qed.
Lemma lem3785483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785484 {A : Type'} (t : type686 A) : (term600 A t) = (term600 A t).
Proof. exact (MK_COMB (@lem3785483 A) (@lem3785482 A t)). Qed.
Lemma lem3785485 {A : Type'} : (term602 A) = (term602 A).
Proof. exact (fun_ext (fun t : type686 A => @lem3785484 A t)). Qed.
Lemma lem3785486 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3785487 {A : Type'} : (term604 A) = (term604 A).
Proof. exact (MK_COMB (@lem3785486 A) (@lem3785485 A)). Qed.
Lemma lem3785654 {A : Type'} : (term603 A) = (term604 A).
Proof. exact (TRANS (@lem3785317 A) (@lem3785487 A)). Qed.
Lemma lem3785655 {A : Type'} : (term604 A) = (term603 A).
Proof. exact (SYM (@lem3785654 A)). Qed.
Lemma lem3785656 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term582 A t f s) : term582 A t f s.
Proof. exact (h1). Qed.
Lemma lem3785658 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3785659 {A : Type'} (t : type686 A) : (term585 A t) = (term605 A t).
Proof. exact (@lem3785658 (term585 A t)). Qed.
Lemma lem3785660 {A : Type'} (t : type686 A) : (term605 A t) = (term585 A t).
Proof. exact (SYM (@lem3785659 A t)). Qed.
Lemma lem3785661 {A : Type'} (t : type686 A) (h1 : term606 A t) : term606 A t.
Proof. exact (h1). Qed.
Lemma lem3785667 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term163 A t t' x) = (term163 A t t' x).
Proof. exact (eq_refl (term163 A t t' x)). Qed.
Lemma lem3785668 {A : Type'} (t : type686 A) (x : A) : (term165 A t x) = (term165 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3785667 A t t' x)). Qed.
Lemma lem3785669 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785670 {A : Type'} (t : type686 A) (x : A) : (term166 A t x) = (term166 A t x).
Proof. exact (MK_COMB (@lem3785669 A) (@lem3785668 A t x)). Qed.
Lemma lem3785672 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3785673 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term247 A s t x) = (term247 A s t x).
Proof. exact (MK_COMB (@lem3785672 A s x) (@lem3785670 A t x)). Qed.
Lemma lem3785674 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term168 A s t x) = (term247 A s t x).
Proof. exact (@lem17265 (s x) (term166 A t x)). Qed.
Lemma lem3785675 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term168 A s t x) = (term247 A s t x).
Proof. exact (TRANS (@lem3785674 A s t x) (@lem3785673 A s t x)). Qed.
Lemma lem3785676 {A : Type'} (s : A -> Prop) (t : type686 A) : (term170 A s t) = (term248 A s t).
Proof. exact (fun_ext (fun x : A => @lem3785675 A s t x)). Qed.
Lemma lem3785677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785678 {A : Type'} (s : A -> Prop) (t : type686 A) : (term171 A s t) = (term249 A s t).
Proof. exact (MK_COMB (@lem3785677 A) (@lem3785676 A s t)). Qed.
Lemma lem3785685 {A : Type'} (t : type686 A) (f : type686 A) (x : A -> Prop) : (term574 A t f x) = (term607 A t f x).
Proof. exact (@lem17265 (t x) (f x)). Qed.
Lemma lem3785686 {A : Type'} (t : type686 A) (f : type686 A) : (term576 A t f) = (term608 A t f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785685 A t f x)). Qed.
Lemma lem3785687 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785688 {A : Type'} (t : type686 A) (f : type686 A) : (term577 A t f) = (term609 A t f).
Proof. exact (MK_COMB (@lem3785687 A) (@lem3785686 A t f)). Qed.
Lemma lem3785692 {A : Type'} (t : type686 A) (x : A -> Prop) : (term237 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3785693 {A : Type'} (P : type686 A) : (term238 A P) = (term239 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3785694 {A : Type'} (t : type686 A) : (term158 A t) = (term240 A t).
Proof. exact (@lem3785693 A (term136 A t)). Qed.
Lemma lem3785695 {A : Type'} (t : type686 A) (x : A -> Prop) : (term241 A t x) = (term134 A t x).
Proof. exact (eq_refl (term241 A t x)). Qed.
Lemma lem3785696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3785697 {A : Type'} (t : type686 A) (x : A -> Prop) : (term242 A t x) = (term237 A t x).
Proof. exact (MK_COMB (@lem3785696) (@lem3785695 A t x)). Qed.
Lemma lem3785698 {A : Type'} (t : type686 A) (x : A -> Prop) : (term242 A t x) = (t x).
Proof. exact (TRANS (@lem3785697 A t x) (@lem3785692 A t x)). Qed.
Lemma lem3785699 {A : Type'} (t : type686 A) : (term243 A t) = (term244 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785698 A t x)). Qed.
Lemma lem3785700 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785701 {A : Type'} (t : type686 A) : (term240 A t) = (term245 A t).
Proof. exact (MK_COMB (@lem3785700 A) (@lem3785699 A t)). Qed.
Lemma lem3785702 {A : Type'} (t : type686 A) : (term158 A t) = (term245 A t).
Proof. exact (TRANS (@lem3785694 A t) (@lem3785701 A t)). Qed.
Lemma lem3785709 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term222 A t f u) = (term223 A t f u).
Proof. exact (@lem17045 (f t) (f u)). Qed.
Lemma lem3785716 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term146 A t u x) = (term224 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3785717 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term148 A t u) = (term225 A t u).
Proof. exact (fun_ext (fun x : A => @lem3785716 A t u x)). Qed.
Lemma lem3785718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785719 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term149 A t u) = (term226 A t u).
Proof. exact (MK_COMB (@lem3785718 A) (@lem3785717 A t u)). Qed.
Lemma lem3785726 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term146 A u t x) = (term224 A u t x).
Proof. exact (@lem17265 (u x) (t x)). Qed.
Lemma lem3785727 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term148 A u t) = (term225 A u t).
Proof. exact (fun_ext (fun x : A => @lem3785726 A u t x)). Qed.
Lemma lem3785728 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785729 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term149 A u t) = (term226 A u t).
Proof. exact (MK_COMB (@lem3785728 A) (@lem3785727 A u t)). Qed.
Lemma lem3785730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3785731 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term150 A t u) = (term227 A t u).
Proof. exact (MK_COMB (@lem3785730) (@lem3785719 A t u)). Qed.
Lemma lem3785732 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term151 A u t) = (term228 A u t).
Proof. exact (MK_COMB (@lem3785731 A t u) (@lem3785729 A u t)). Qed.
Lemma lem3785733 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3785734 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term229 A t f u) = (term230 A t f u).
Proof. exact (MK_COMB (@lem3785733) (@lem3785709 A t f u)). Qed.
Lemma lem3785735 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term231 A f u t) = (term232 A f u t).
Proof. exact (MK_COMB (@lem3785734 A t f u) (@lem3785732 A u t)). Qed.
Lemma lem3785736 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term231 A f u t).
Proof. exact (@lem17265 (term141 A t f u) (term151 A u t)). Qed.
Lemma lem3785737 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term152 A f u t) = (term232 A f u t).
Proof. exact (TRANS (@lem3785736 A f u t) (@lem3785735 A f u t)). Qed.
Lemma lem3785738 {A : Type'} (f : type686 A) (t : A -> Prop) : (term153 A f t) = (term233 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3785737 A f u t)). Qed.
Lemma lem3785739 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785740 {A : Type'} (f : type686 A) (t : A -> Prop) : (term154 A f t) = (term234 A f t).
Proof. exact (MK_COMB (@lem3785739 A) (@lem3785738 A f t)). Qed.
Lemma lem3785741 {A : Type'} (f : type686 A) : (term155 A f) = (term235 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3785740 A f t)). Qed.
Lemma lem3785742 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3785743 {A : Type'} (f : type686 A) : (term156 A f) = (term236 A f).
Proof. exact (MK_COMB (@lem3785742 A) (@lem3785741 A f)). Qed.
Lemma lem3785746 {A : Type'} (f : type686 A) (x : A -> Prop) : (term237 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3785747 {A : Type'} (P : type686 A) : (term238 A P) = (term239 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3785748 {A : Type'} (f : type686 A) : (term158 A f) = (term240 A f).
Proof. exact (@lem3785747 A (term136 A f)). Qed.
Lemma lem3785749 {A : Type'} (f : type686 A) (x : A -> Prop) : (term241 A f x) = (term134 A f x).
Proof. exact (eq_refl (term241 A f x)). Qed.
Lemma lem3785750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3785751 {A : Type'} (f : type686 A) (x : A -> Prop) : (term242 A f x) = (term237 A f x).
Proof. exact (MK_COMB (@lem3785750) (@lem3785749 A f x)). Qed.
Lemma lem3785752 {A : Type'} (f : type686 A) (x : A -> Prop) : (term242 A f x) = (f x).
Proof. exact (TRANS (@lem3785751 A f x) (@lem3785746 A f x)). Qed.
Lemma lem3785753 {A : Type'} (f : type686 A) : (term243 A f) = (term244 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3785752 A f x)). Qed.
Lemma lem3785754 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785755 {A : Type'} (f : type686 A) : (term240 A f) = (term245 A f).
Proof. exact (MK_COMB (@lem3785754 A) (@lem3785753 A f)). Qed.
Lemma lem3785756 {A : Type'} (f : type686 A) : (term158 A f) = (term245 A f).
Proof. exact (TRANS (@lem3785748 A f) (@lem3785755 A f)). Qed.
Lemma lem3785762 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term163 A f t x) = (term163 A f t x).
Proof. exact (eq_refl (term163 A f t x)). Qed.
Lemma lem3785763 {A : Type'} (f : type686 A) (x : A) : (term165 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3785762 A f t x)). Qed.
Lemma lem3785764 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3785765 {A : Type'} (f : type686 A) (x : A) : (term166 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3785764 A) (@lem3785763 A f x)). Qed.
Lemma lem3785767 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3785768 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term247 A s f x) = (term247 A s f x).
Proof. exact (MK_COMB (@lem3785767 A s x) (@lem3785765 A f x)). Qed.
Lemma lem3785769 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term247 A s f x).
Proof. exact (@lem17265 (s x) (term166 A f x)). Qed.
Lemma lem3785770 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term168 A s f x) = (term247 A s f x).
Proof. exact (TRANS (@lem3785769 A s f x) (@lem3785768 A s f x)). Qed.
Lemma lem3785771 {A : Type'} (s : A -> Prop) (f : type686 A) : (term170 A s f) = (term248 A s f).
Proof. exact (fun_ext (fun x : A => @lem3785770 A s f x)). Qed.
Lemma lem3785772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3785773 {A : Type'} (s : A -> Prop) (f : type686 A) : (term171 A s f) = (term249 A s f).
Proof. exact (MK_COMB (@lem3785772 A) (@lem3785771 A s f)). Qed.
Lemma lem3785774 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3785775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785776 {A : Type'} (s : A -> Prop) (f : type686 A) : (term172 A s f) = (term250 A s f).
Proof. exact (MK_COMB (@lem3785775) (@lem3785773 A s f)). Qed.
Lemma lem3785777 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term251 A f s).
Proof. exact (MK_COMB (@lem3785776 A s f) (@lem3785774 A s)). Qed.
Lemma lem3785778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785779 {A : Type'} (f : type686 A) : (term159 A f) = (term252 A f).
Proof. exact (MK_COMB (@lem3785778) (@lem3785756 A f)). Qed.
Lemma lem3785780 {A : Type'} (f : type686 A) (s : A -> Prop) : (term174 A f s) = (term253 A f s).
Proof. exact (MK_COMB (@lem3785779 A f) (@lem3785777 A f s)). Qed.
Lemma lem3785781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785782 {A : Type'} (f : type686 A) : (term157 A f) = (term254 A f).
Proof. exact (MK_COMB (@lem3785781) (@lem3785743 A f)). Qed.
Lemma lem3785783 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term255 A f s).
Proof. exact (MK_COMB (@lem3785782 A f) (@lem3785780 A f s)). Qed.
Lemma lem3785784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785785 {A : Type'} (t : type686 A) : (term159 A t) = (term252 A t).
Proof. exact (MK_COMB (@lem3785784) (@lem3785702 A t)). Qed.
Lemma lem3785786 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term579 A t f s) = (term610 A t f s).
Proof. exact (MK_COMB (@lem3785785 A t) (@lem3785783 A f s)). Qed.
Lemma lem3785788 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3785789 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term580 A t f s) = (term611 A t f s).
Proof. exact (MK_COMB (@lem3785788 A t) (@lem3785786 A t f s)). Qed.
Lemma lem3785790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785791 {A : Type'} (t : type686 A) (f : type686 A) : (term578 A t f) = (term612 A t f).
Proof. exact (MK_COMB (@lem3785790) (@lem3785688 A t f)). Qed.
Lemma lem3785792 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term581 A t f s) = (term613 A t f s).
Proof. exact (MK_COMB (@lem3785791 A t f) (@lem3785789 A t f s)). Qed.
Lemma lem3785793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3785794 {A : Type'} (s : A -> Prop) (t : type686 A) : (term172 A s t) = (term250 A s t).
Proof. exact (MK_COMB (@lem3785793) (@lem3785678 A s t)). Qed.
Lemma lem3785795 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term582 A t f s) = (term614 A t f s).
Proof. exact (MK_COMB (@lem3785794 A s t) (@lem3785792 A t f s)). Qed.
Lemma lem3786106 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786107 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3786106 (A -> Prop) P Q). Qed.
Lemma lem3786108 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term261 A s t x) = (term262 A s t x).
Proof. exact (@lem3786107 A (term188 A s x) (term165 A t x)). Qed.
Lemma lem3786109 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term263 A t x t') = (term163 A t t' x).
Proof. exact (eq_refl (term263 A t x t')). Qed.
Lemma lem3786110 {A : Type'} (t : type686 A) (x : A) : (term264 A t x) = (term165 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786109 A t t' x)). Qed.
Lemma lem3786111 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786112 {A : Type'} (t : type686 A) (x : A) : (term265 A t x) = (term166 A t x).
Proof. exact (MK_COMB (@lem3786111 A) (@lem3786110 A t x)). Qed.
Lemma lem3786113 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3786114 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term261 A s t x) = (term247 A s t x).
Proof. exact (MK_COMB (@lem3786113 A s x) (@lem3786112 A t x)). Qed.
Lemma lem3786115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786116 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term266 A s t x) = (term267 A s t x).
Proof. exact (MK_COMB (@lem3786115) (@lem3786114 A s t x)). Qed.
Lemma lem3786117 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term263 A t x t') = (term163 A t t' x).
Proof. exact (eq_refl (term263 A t x t')). Qed.
Lemma lem3786118 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3786119 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) (x : A) : (term268 A s t x t') = (term269 A s t t' x).
Proof. exact (MK_COMB (@lem3786118 A s x) (@lem3786117 A t t' x)). Qed.
Lemma lem3786120 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term270 A s t x) = (term271 A s t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786119 A s t t' x)). Qed.
Lemma lem3786121 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786122 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term262 A s t x) = (term272 A s t x).
Proof. exact (MK_COMB (@lem3786121 A) (@lem3786120 A s t x)). Qed.
Lemma lem3786123 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : ((term261 A s t x) = (term262 A s t x)) = ((term247 A s t x) = (term272 A s t x)).
Proof. exact (MK_COMB (@lem3786116 A s t x) (@lem3786122 A s t x)). Qed.
Lemma lem3786124 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term247 A s t x) = (term272 A s t x).
Proof. exact (EQ_MP (@lem3786123 A s t x) (@lem3786108 A s t x)). Qed.
Lemma lem3786125 {A : Type'} (s : A -> Prop) (t : type686 A) : (term248 A s t) = (term273 A s t).
Proof. exact (fun_ext (fun x : A => @lem3786124 A s t x)). Qed.
Lemma lem3786126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786127 {A : Type'} (s : A -> Prop) (t : type686 A) : (term249 A s t) = (term274 A s t).
Proof. exact (MK_COMB (@lem3786126 A) (@lem3786125 A s t)). Qed.
Lemma lem3786129 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3786130 {A : Type'} (P : type1364 A) : (term277 A P) = (term278 A P).
Proof. exact (@lem3786129 A (A -> Prop) P). Qed.
Lemma lem3786131 {A : Type'} (s : A -> Prop) (t : type686 A) : (term279 A s t) = (term280 A s t).
Proof. exact (@lem3786130 A (term281 A s t)). Qed.
Lemma lem3786132 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term282 A s t x) = (term271 A s t x).
Proof. exact (eq_refl (term282 A s t x)). Qed.
Lemma lem3786133 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3786134 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) : (term283 A s t x t') = (term284 A s t x t').
Proof. exact (MK_COMB (@lem3786132 A s t x) (@lem3786133 A t')). Qed.
Lemma lem3786135 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) (x : A) : (term284 A s t x t') = (term269 A s t t' x).
Proof. exact (eq_refl (term284 A s t x t')). Qed.
Lemma lem3786136 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) (x : A) : (term283 A s t x t') = (term269 A s t t' x).
Proof. exact (TRANS (@lem3786134 A s t x t') (@lem3786135 A s t t' x)). Qed.
Lemma lem3786137 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term285 A s t x) = (term271 A s t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786136 A s t t' x)). Qed.
Lemma lem3786138 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786139 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term286 A s t x) = (term272 A s t x).
Proof. exact (MK_COMB (@lem3786138 A) (@lem3786137 A s t x)). Qed.
Lemma lem3786140 {A : Type'} (s : A -> Prop) (t : type686 A) : (term287 A s t) = (term273 A s t).
Proof. exact (fun_ext (fun x : A => @lem3786139 A s t x)). Qed.
Lemma lem3786141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786142 {A : Type'} (s : A -> Prop) (t : type686 A) : (term279 A s t) = (term274 A s t).
Proof. exact (MK_COMB (@lem3786141 A) (@lem3786140 A s t)). Qed.
Lemma lem3786143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786144 {A : Type'} (s : A -> Prop) (t : type686 A) : (term288 A s t) = (term289 A s t).
Proof. exact (MK_COMB (@lem3786143) (@lem3786142 A s t)). Qed.
Lemma lem3786145 {A : Type'} (s : A -> Prop) (t : type686 A) (x : A) : (term282 A s t x) = (term271 A s t x).
Proof. exact (eq_refl (term282 A s t x)). Qed.
Lemma lem3786146 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3786147 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) (x : A) : (term290 A s t t' x) = (term291 A s t t' x).
Proof. exact (MK_COMB (@lem3786145 A s t x) (@lem3786146 A t' x)). Qed.
Lemma lem3786148 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) (x : A) : (term291 A s t t' x) = (term292 A s t t' x).
Proof. exact (eq_refl (term291 A s t t' x)). Qed.
Lemma lem3786149 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) (x : A) : (term290 A s t t' x) = (term292 A s t t' x).
Proof. exact (TRANS (@lem3786147 A s t t' x) (@lem3786148 A s t t' x)). Qed.
Lemma lem3786150 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term293 A s t t') = (term294 A s t t').
Proof. exact (fun_ext (fun x : A => @lem3786149 A s t t' x)). Qed.
Lemma lem3786151 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786152 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term295 A s t t') = (term296 A s t t').
Proof. exact (MK_COMB (@lem3786151 A) (@lem3786150 A s t t')). Qed.
Lemma lem3786153 {A : Type'} (s : A -> Prop) (t : type686 A) : (term297 A s t) = (term298 A s t).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786152 A s t t')). Qed.
Lemma lem3786154 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786155 {A : Type'} (s : A -> Prop) (t : type686 A) : (term280 A s t) = (term299 A s t).
Proof. exact (MK_COMB (@lem3786154 A) (@lem3786153 A s t)). Qed.
Lemma lem3786156 {A : Type'} (s : A -> Prop) (t : type686 A) : ((term279 A s t) = (term280 A s t)) = ((term274 A s t) = (term299 A s t)).
Proof. exact (MK_COMB (@lem3786144 A s t) (@lem3786155 A s t)). Qed.
Lemma lem3786157 {A : Type'} (s : A -> Prop) (t : type686 A) : (term274 A s t) = (term299 A s t).
Proof. exact (EQ_MP (@lem3786156 A s t) (@lem3786131 A s t)). Qed.
Lemma lem3786158 {A : Type'} (s : A -> Prop) (t : type686 A) : (term249 A s t) = (term299 A s t).
Proof. exact (TRANS (@lem3786127 A s t) (@lem3786157 A s t)). Qed.
Lemma lem3786159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786160 {A : Type'} (s : A -> Prop) (t : type686 A) : (term250 A s t) = (term300 A s t).
Proof. exact (MK_COMB (@lem3786159) (@lem3786158 A s t)). Qed.
Lemma lem3786162 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786163 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3786162 (A -> Prop) P Q). Qed.
Lemma lem3786164 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term261 A s f x) = (term262 A s f x).
Proof. exact (@lem3786163 A (term188 A s x) (term165 A f x)). Qed.
Lemma lem3786165 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term263 A f x t) = (term163 A f t x).
Proof. exact (eq_refl (term263 A f x t)). Qed.
Lemma lem3786166 {A : Type'} (f : type686 A) (x : A) : (term264 A f x) = (term165 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3786165 A f t x)). Qed.
Lemma lem3786167 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786168 {A : Type'} (f : type686 A) (x : A) : (term265 A f x) = (term166 A f x).
Proof. exact (MK_COMB (@lem3786167 A) (@lem3786166 A f x)). Qed.
Lemma lem3786169 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3786170 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term261 A s f x) = (term247 A s f x).
Proof. exact (MK_COMB (@lem3786169 A s x) (@lem3786168 A f x)). Qed.
Lemma lem3786171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786172 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term266 A s f x) = (term267 A s f x).
Proof. exact (MK_COMB (@lem3786171) (@lem3786170 A s f x)). Qed.
Lemma lem3786173 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term263 A f x t) = (term163 A f t x).
Proof. exact (eq_refl (term263 A f x t)). Qed.
Lemma lem3786174 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term246 A s x).
Proof. exact (eq_refl (term246 A s x)). Qed.
Lemma lem3786175 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term268 A s f x t) = (term269 A s f t x).
Proof. exact (MK_COMB (@lem3786174 A s x) (@lem3786173 A f t x)). Qed.
Lemma lem3786176 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term270 A s f x) = (term271 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3786175 A s f t x)). Qed.
Lemma lem3786177 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786178 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term262 A s f x) = (term272 A s f x).
Proof. exact (MK_COMB (@lem3786177 A) (@lem3786176 A s f x)). Qed.
Lemma lem3786179 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term261 A s f x) = (term262 A s f x)) = ((term247 A s f x) = (term272 A s f x)).
Proof. exact (MK_COMB (@lem3786172 A s f x) (@lem3786178 A s f x)). Qed.
Lemma lem3786180 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term247 A s f x) = (term272 A s f x).
Proof. exact (EQ_MP (@lem3786179 A s f x) (@lem3786164 A s f x)). Qed.
Lemma lem3786181 {A : Type'} (s : A -> Prop) (f : type686 A) : (term248 A s f) = (term273 A s f).
Proof. exact (fun_ext (fun x : A => @lem3786180 A s f x)). Qed.
Lemma lem3786182 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786183 {A : Type'} (s : A -> Prop) (f : type686 A) : (term249 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem3786182 A) (@lem3786181 A s f)). Qed.
Lemma lem3786185 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3786186 {A : Type'} (P : type1364 A) : (term277 A P) = (term278 A P).
Proof. exact (@lem3786185 A (A -> Prop) P). Qed.
Lemma lem3786187 {A : Type'} (s : A -> Prop) (f : type686 A) : (term279 A s f) = (term280 A s f).
Proof. exact (@lem3786186 A (term281 A s f)). Qed.
Lemma lem3786188 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term282 A s f x) = (term271 A s f x).
Proof. exact (eq_refl (term282 A s f x)). Qed.
Lemma lem3786189 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3786190 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term283 A s f x t) = (term284 A s f x t).
Proof. exact (MK_COMB (@lem3786188 A s f x) (@lem3786189 A t)). Qed.
Lemma lem3786191 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term284 A s f x t) = (term269 A s f t x).
Proof. exact (eq_refl (term284 A s f x t)). Qed.
Lemma lem3786192 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term283 A s f x t) = (term269 A s f t x).
Proof. exact (TRANS (@lem3786190 A s f x t) (@lem3786191 A s f t x)). Qed.
Lemma lem3786193 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term285 A s f x) = (term271 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3786192 A s f t x)). Qed.
Lemma lem3786194 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786195 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term286 A s f x) = (term272 A s f x).
Proof. exact (MK_COMB (@lem3786194 A) (@lem3786193 A s f x)). Qed.
Lemma lem3786196 {A : Type'} (s : A -> Prop) (f : type686 A) : (term287 A s f) = (term273 A s f).
Proof. exact (fun_ext (fun x : A => @lem3786195 A s f x)). Qed.
Lemma lem3786197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786198 {A : Type'} (s : A -> Prop) (f : type686 A) : (term279 A s f) = (term274 A s f).
Proof. exact (MK_COMB (@lem3786197 A) (@lem3786196 A s f)). Qed.
Lemma lem3786199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786200 {A : Type'} (s : A -> Prop) (f : type686 A) : (term288 A s f) = (term289 A s f).
Proof. exact (MK_COMB (@lem3786199) (@lem3786198 A s f)). Qed.
Lemma lem3786201 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term282 A s f x) = (term271 A s f x).
Proof. exact (eq_refl (term282 A s f x)). Qed.
Lemma lem3786202 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3786203 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term290 A s f t x) = (term291 A s f t x).
Proof. exact (MK_COMB (@lem3786201 A s f x) (@lem3786202 A t x)). Qed.
Lemma lem3786204 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term291 A s f t x) = (term292 A s f t x).
Proof. exact (eq_refl (term291 A s f t x)). Qed.
Lemma lem3786205 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term290 A s f t x) = (term292 A s f t x).
Proof. exact (TRANS (@lem3786203 A s f t x) (@lem3786204 A s f t x)). Qed.
Lemma lem3786206 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term293 A s f t) = (term294 A s f t).
Proof. exact (fun_ext (fun x : A => @lem3786205 A s f t x)). Qed.
Lemma lem3786207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3786208 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term295 A s f t) = (term296 A s f t).
Proof. exact (MK_COMB (@lem3786207 A) (@lem3786206 A s f t)). Qed.
Lemma lem3786209 {A : Type'} (s : A -> Prop) (f : type686 A) : (term297 A s f) = (term298 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786208 A s f t)). Qed.
Lemma lem3786210 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786211 {A : Type'} (s : A -> Prop) (f : type686 A) : (term280 A s f) = (term299 A s f).
Proof. exact (MK_COMB (@lem3786210 A) (@lem3786209 A s f)). Qed.
Lemma lem3786212 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term279 A s f) = (term280 A s f)) = ((term274 A s f) = (term299 A s f)).
Proof. exact (MK_COMB (@lem3786200 A s f) (@lem3786211 A s f)). Qed.
Lemma lem3786213 {A : Type'} (s : A -> Prop) (f : type686 A) : (term274 A s f) = (term299 A s f).
Proof. exact (EQ_MP (@lem3786212 A s f) (@lem3786187 A s f)). Qed.
Lemma lem3786214 {A : Type'} (s : A -> Prop) (f : type686 A) : (term249 A s f) = (term299 A s f).
Proof. exact (TRANS (@lem3786183 A s f) (@lem3786213 A s f)). Qed.
Lemma lem3786215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786216 {A : Type'} (s : A -> Prop) (f : type686 A) : (term250 A s f) = (term300 A s f).
Proof. exact (MK_COMB (@lem3786215) (@lem3786214 A s f)). Qed.
Lemma lem3786217 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3786218 {A : Type'} (f : type686 A) (s : A -> Prop) : (term251 A f s) = (term301 A f s).
Proof. exact (MK_COMB (@lem3786216 A s f) (@lem3786217 A s)). Qed.
Lemma lem3786220 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3786221 {A : Type'} (P : type421 A) (Q : Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (@lem3786220 (type1402 A) P Q). Qed.
Lemma lem3786222 {A : Type'} (f : type686 A) (s : A -> Prop) : (term306 A f s) = (term307 A f s).
Proof. exact (@lem3786221 A (term298 A s f) (@FINITE A s)). Qed.
Lemma lem3786223 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term308 A s f t) = (term296 A s f t).
Proof. exact (eq_refl (term308 A s f t)). Qed.
Lemma lem3786224 {A : Type'} (s : A -> Prop) (f : type686 A) : (term309 A s f) = (term298 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786223 A s f t)). Qed.
Lemma lem3786225 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786226 {A : Type'} (s : A -> Prop) (f : type686 A) : (term310 A s f) = (term299 A s f).
Proof. exact (MK_COMB (@lem3786225 A) (@lem3786224 A s f)). Qed.
Lemma lem3786227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786228 {A : Type'} (s : A -> Prop) (f : type686 A) : (term311 A s f) = (term300 A s f).
Proof. exact (MK_COMB (@lem3786227) (@lem3786226 A s f)). Qed.
Lemma lem3786229 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3786230 {A : Type'} (f : type686 A) (s : A -> Prop) : (term306 A f s) = (term301 A f s).
Proof. exact (MK_COMB (@lem3786228 A s f) (@lem3786229 A s)). Qed.
Lemma lem3786231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786232 {A : Type'} (f : type686 A) (s : A -> Prop) : (term312 A f s) = (term313 A f s).
Proof. exact (MK_COMB (@lem3786231) (@lem3786230 A f s)). Qed.
Lemma lem3786233 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term308 A s f t) = (term296 A s f t).
Proof. exact (eq_refl (term308 A s f t)). Qed.
Lemma lem3786234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786235 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term314 A s f t) = (term315 A s f t).
Proof. exact (MK_COMB (@lem3786234) (@lem3786233 A s f t)). Qed.
Lemma lem3786236 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3786237 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term316 A f t s) = (term317 A f t s).
Proof. exact (MK_COMB (@lem3786235 A s f t) (@lem3786236 A s)). Qed.
Lemma lem3786238 {A : Type'} (f : type686 A) (s : A -> Prop) : (term318 A f s) = (term319 A f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786237 A f t s)). Qed.
Lemma lem3786239 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786240 {A : Type'} (f : type686 A) (s : A -> Prop) : (term307 A f s) = (term320 A f s).
Proof. exact (MK_COMB (@lem3786239 A) (@lem3786238 A f s)). Qed.
Lemma lem3786241 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term306 A f s) = (term307 A f s)) = ((term301 A f s) = (term320 A f s)).
Proof. exact (MK_COMB (@lem3786232 A f s) (@lem3786240 A f s)). Qed.
Lemma lem3786242 {A : Type'} (f : type686 A) (s : A -> Prop) : (term301 A f s) = (term320 A f s).
Proof. exact (EQ_MP (@lem3786241 A f s) (@lem3786222 A f s)). Qed.
Lemma lem3786243 {A : Type'} (f : type686 A) (s : A -> Prop) : (term251 A f s) = (term320 A f s).
Proof. exact (TRANS (@lem3786218 A f s) (@lem3786242 A f s)). Qed.
Lemma lem3786244 {A : Type'} (f : type686 A) : (term252 A f) = (term252 A f).
Proof. exact (eq_refl (term252 A f)). Qed.
Lemma lem3786245 {A : Type'} (f : type686 A) (s : A -> Prop) : (term253 A f s) = (term321 A f s).
Proof. exact (MK_COMB (@lem3786244 A f) (@lem3786243 A f s)). Qed.
Lemma lem3786247 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3786248 {A : Type'} (P : type686 A) (Q : Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem3786247 (A -> Prop) P Q). Qed.
Lemma lem3786249 {A : Type'} (f : type686 A) (s : A -> Prop) : (term321 A f s) = (term324 A f s).
Proof. exact (@lem3786248 A f (term320 A f s)). Qed.
Lemma lem3786251 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786252 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786251 (type1402 A) P Q). Qed.
Lemma lem3786253 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term329 A x f s) = (term330 A x f s).
Proof. exact (@lem3786252 A (f x) (term319 A f s)). Qed.
Lemma lem3786254 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term331 A f s t) = (term317 A f t s).
Proof. exact (eq_refl (term331 A f s t)). Qed.
Lemma lem3786255 {A : Type'} (f : type686 A) (s : A -> Prop) : (term332 A f s) = (term319 A f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786254 A f t s)). Qed.
Lemma lem3786256 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786257 {A : Type'} (f : type686 A) (s : A -> Prop) : (term333 A f s) = (term320 A f s).
Proof. exact (MK_COMB (@lem3786256 A) (@lem3786255 A f s)). Qed.
Lemma lem3786258 {A : Type'} (f : type686 A) (x : A -> Prop) : (term139 A f x) = (term139 A f x).
Proof. exact (eq_refl (term139 A f x)). Qed.
Lemma lem3786259 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term329 A x f s) = (term334 A x f s).
Proof. exact (MK_COMB (@lem3786258 A f x) (@lem3786257 A f s)). Qed.
Lemma lem3786260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786261 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term335 A x f s) = (term336 A x f s).
Proof. exact (MK_COMB (@lem3786260) (@lem3786259 A x f s)). Qed.
Lemma lem3786262 {A : Type'} (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term331 A f s t) = (term317 A f t s).
Proof. exact (eq_refl (term331 A f s t)). Qed.
Lemma lem3786263 {A : Type'} (f : type686 A) (x : A -> Prop) : (term139 A f x) = (term139 A f x).
Proof. exact (eq_refl (term139 A f x)). Qed.
Lemma lem3786264 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term337 A x f s t) = (term338 A x f t s).
Proof. exact (MK_COMB (@lem3786263 A f x) (@lem3786262 A f t s)). Qed.
Lemma lem3786265 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term339 A x f s) = (term340 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786264 A x f t s)). Qed.
Lemma lem3786266 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786267 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term330 A x f s) = (term341 A x f s).
Proof. exact (MK_COMB (@lem3786266 A) (@lem3786265 A x f s)). Qed.
Lemma lem3786268 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term329 A x f s) = (term330 A x f s)) = ((term334 A x f s) = (term341 A x f s)).
Proof. exact (MK_COMB (@lem3786261 A x f s) (@lem3786267 A x f s)). Qed.
Lemma lem3786269 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term334 A x f s) = (term341 A x f s).
Proof. exact (EQ_MP (@lem3786268 A x f s) (@lem3786253 A x f s)). Qed.
Lemma lem3786270 {A : Type'} (f : type686 A) (s : A -> Prop) : (term342 A f s) = (term343 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786269 A x f s)). Qed.
Lemma lem3786271 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786272 {A : Type'} (f : type686 A) (s : A -> Prop) : (term324 A f s) = (term344 A f s).
Proof. exact (MK_COMB (@lem3786271 A) (@lem3786270 A f s)). Qed.
Lemma lem3786273 {A : Type'} (f : type686 A) (s : A -> Prop) : (term321 A f s) = (term344 A f s).
Proof. exact (TRANS (@lem3786249 A f s) (@lem3786272 A f s)). Qed.
Lemma lem3786274 {A : Type'} (f : type686 A) (s : A -> Prop) : (term253 A f s) = (term344 A f s).
Proof. exact (TRANS (@lem3786245 A f s) (@lem3786273 A f s)). Qed.
Lemma lem3786275 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3786276 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term345 A f s).
Proof. exact (MK_COMB (@lem3786275 A f) (@lem3786274 A f s)). Qed.
Lemma lem3786278 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786279 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786278 (A -> Prop) P Q). Qed.
Lemma lem3786280 {A : Type'} (f : type686 A) (s : A -> Prop) : (term348 A f s) = (term349 A f s).
Proof. exact (@lem3786279 A (term236 A f) (term343 A f s)). Qed.
Lemma lem3786281 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term350 A f s x) = (term341 A x f s).
Proof. exact (eq_refl (term350 A f s x)). Qed.
Lemma lem3786282 {A : Type'} (f : type686 A) (s : A -> Prop) : (term351 A f s) = (term343 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786281 A x f s)). Qed.
Lemma lem3786283 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786284 {A : Type'} (f : type686 A) (s : A -> Prop) : (term352 A f s) = (term344 A f s).
Proof. exact (MK_COMB (@lem3786283 A) (@lem3786282 A f s)). Qed.
Lemma lem3786285 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3786286 {A : Type'} (f : type686 A) (s : A -> Prop) : (term348 A f s) = (term345 A f s).
Proof. exact (MK_COMB (@lem3786285 A f) (@lem3786284 A f s)). Qed.
Lemma lem3786287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786288 {A : Type'} (f : type686 A) (s : A -> Prop) : (term353 A f s) = (term354 A f s).
Proof. exact (MK_COMB (@lem3786287) (@lem3786286 A f s)). Qed.
Lemma lem3786289 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term350 A f s x) = (term341 A x f s).
Proof. exact (eq_refl (term350 A f s x)). Qed.
Lemma lem3786290 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3786291 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term355 A f s x) = (term356 A x f s).
Proof. exact (MK_COMB (@lem3786290 A f) (@lem3786289 A x f s)). Qed.
Lemma lem3786292 {A : Type'} (f : type686 A) (s : A -> Prop) : (term357 A f s) = (term358 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786291 A x f s)). Qed.
Lemma lem3786293 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786294 {A : Type'} (f : type686 A) (s : A -> Prop) : (term349 A f s) = (term359 A f s).
Proof. exact (MK_COMB (@lem3786293 A) (@lem3786292 A f s)). Qed.
Lemma lem3786295 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term348 A f s) = (term349 A f s)) = ((term345 A f s) = (term359 A f s)).
Proof. exact (MK_COMB (@lem3786288 A f s) (@lem3786294 A f s)). Qed.
Lemma lem3786296 {A : Type'} (f : type686 A) (s : A -> Prop) : (term345 A f s) = (term359 A f s).
Proof. exact (EQ_MP (@lem3786295 A f s) (@lem3786280 A f s)). Qed.
Lemma lem3786298 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786299 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786298 (type1402 A) P Q). Qed.
Lemma lem3786300 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term360 A x f s) = (term361 A x f s).
Proof. exact (@lem3786299 A (term236 A f) (term340 A x f s)). Qed.
Lemma lem3786301 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term362 A x f s t) = (term338 A x f t s).
Proof. exact (eq_refl (term362 A x f s t)). Qed.
Lemma lem3786302 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term363 A x f s) = (term340 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786301 A x f t s)). Qed.
Lemma lem3786303 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786304 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term364 A x f s) = (term341 A x f s).
Proof. exact (MK_COMB (@lem3786303 A) (@lem3786302 A x f s)). Qed.
Lemma lem3786305 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3786306 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term360 A x f s) = (term356 A x f s).
Proof. exact (MK_COMB (@lem3786305 A f) (@lem3786304 A x f s)). Qed.
Lemma lem3786307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786308 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term365 A x f s) = (term366 A x f s).
Proof. exact (MK_COMB (@lem3786307) (@lem3786306 A x f s)). Qed.
Lemma lem3786309 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term362 A x f s t) = (term338 A x f t s).
Proof. exact (eq_refl (term362 A x f s t)). Qed.
Lemma lem3786310 {A : Type'} (f : type686 A) : (term254 A f) = (term254 A f).
Proof. exact (eq_refl (term254 A f)). Qed.
Lemma lem3786311 {A : Type'} (x : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term367 A x f s t) = (term368 A x f t s).
Proof. exact (MK_COMB (@lem3786310 A f) (@lem3786309 A x f t s)). Qed.
Lemma lem3786312 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term369 A x f s) = (term370 A x f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786311 A x f t s)). Qed.
Lemma lem3786313 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786314 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term361 A x f s) = (term371 A x f s).
Proof. exact (MK_COMB (@lem3786313 A) (@lem3786312 A x f s)). Qed.
Lemma lem3786315 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term360 A x f s) = (term361 A x f s)) = ((term356 A x f s) = (term371 A x f s)).
Proof. exact (MK_COMB (@lem3786308 A x f s) (@lem3786314 A x f s)). Qed.
Lemma lem3786316 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term356 A x f s) = (term371 A x f s).
Proof. exact (EQ_MP (@lem3786315 A x f s) (@lem3786300 A x f s)). Qed.
Lemma lem3786317 {A : Type'} (f : type686 A) (s : A -> Prop) : (term358 A f s) = (term372 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786316 A x f s)). Qed.
Lemma lem3786318 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786319 {A : Type'} (f : type686 A) (s : A -> Prop) : (term359 A f s) = (term373 A f s).
Proof. exact (MK_COMB (@lem3786318 A) (@lem3786317 A f s)). Qed.
Lemma lem3786320 {A : Type'} (f : type686 A) (s : A -> Prop) : (term345 A f s) = (term373 A f s).
Proof. exact (TRANS (@lem3786296 A f s) (@lem3786319 A f s)). Qed.
Lemma lem3786321 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term373 A f s).
Proof. exact (TRANS (@lem3786276 A f s) (@lem3786320 A f s)). Qed.
Lemma lem3786322 {A : Type'} (t : type686 A) : (term252 A t) = (term252 A t).
Proof. exact (eq_refl (term252 A t)). Qed.
Lemma lem3786323 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term610 A t f s) = (term615 A t f s).
Proof. exact (MK_COMB (@lem3786322 A t) (@lem3786321 A f s)). Qed.
Lemma lem3786325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3786326 {A : Type'} (P : type686 A) (Q : Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem3786325 (A -> Prop) P Q). Qed.
Lemma lem3786327 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term615 A t f s) = (term616 A t f s).
Proof. exact (@lem3786326 A t (term373 A f s)). Qed.
Lemma lem3786329 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786330 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786329 (A -> Prop) P Q). Qed.
Lemma lem3786331 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term617 A t x f s) = (term618 A t x f s).
Proof. exact (@lem3786330 A (t x) (term372 A f s)). Qed.
Lemma lem3786332 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term377 A f s x) = (term371 A x f s).
Proof. exact (eq_refl (term377 A f s x)). Qed.
Lemma lem3786333 {A : Type'} (f : type686 A) (s : A -> Prop) : (term378 A f s) = (term372 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786332 A x f s)). Qed.
Lemma lem3786334 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786335 {A : Type'} (f : type686 A) (s : A -> Prop) : (term379 A f s) = (term373 A f s).
Proof. exact (MK_COMB (@lem3786334 A) (@lem3786333 A f s)). Qed.
Lemma lem3786336 {A : Type'} (t : type686 A) (x : A -> Prop) : (term139 A t x) = (term139 A t x).
Proof. exact (eq_refl (term139 A t x)). Qed.
Lemma lem3786337 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term617 A t x f s) = (term619 A t x f s).
Proof. exact (MK_COMB (@lem3786336 A t x) (@lem3786335 A f s)). Qed.
Lemma lem3786338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786339 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term620 A t x f s) = (term621 A t x f s).
Proof. exact (MK_COMB (@lem3786338) (@lem3786337 A t x f s)). Qed.
Lemma lem3786340 {A : Type'} (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term377 A f s x') = (term371 A x' f s).
Proof. exact (eq_refl (term377 A f s x')). Qed.
Lemma lem3786341 {A : Type'} (t : type686 A) (x : A -> Prop) : (term139 A t x) = (term139 A t x).
Proof. exact (eq_refl (term139 A t x)). Qed.
Lemma lem3786342 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term622 A t x f s x') = (term623 A t x x' f s).
Proof. exact (MK_COMB (@lem3786341 A t x) (@lem3786340 A x' f s)). Qed.
Lemma lem3786343 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term624 A t x f s) = (term625 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786342 A t x x' f s)). Qed.
Lemma lem3786344 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786345 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term618 A t x f s) = (term626 A t x f s).
Proof. exact (MK_COMB (@lem3786344 A) (@lem3786343 A t x f s)). Qed.
Lemma lem3786346 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term617 A t x f s) = (term618 A t x f s)) = ((term619 A t x f s) = (term626 A t x f s)).
Proof. exact (MK_COMB (@lem3786339 A t x f s) (@lem3786345 A t x f s)). Qed.
Lemma lem3786347 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term619 A t x f s) = (term626 A t x f s).
Proof. exact (EQ_MP (@lem3786346 A t x f s) (@lem3786331 A t x f s)). Qed.
Lemma lem3786349 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786350 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786349 (type1402 A) P Q). Qed.
Lemma lem3786351 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term627 A t x x' f s) = (term628 A t x x' f s).
Proof. exact (@lem3786350 A (t x) (term370 A x' f s)). Qed.
Lemma lem3786352 {A : Type'} (x' : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term389 A x' f s t) = (term368 A x' f t s).
Proof. exact (eq_refl (term389 A x' f s t)). Qed.
Lemma lem3786353 {A : Type'} (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term390 A x' f s) = (term370 A x' f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3786352 A x' f t s)). Qed.
Lemma lem3786354 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786355 {A : Type'} (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term391 A x' f s) = (term371 A x' f s).
Proof. exact (MK_COMB (@lem3786354 A) (@lem3786353 A x' f s)). Qed.
Lemma lem3786356 {A : Type'} (t : type686 A) (x : A -> Prop) : (term139 A t x) = (term139 A t x).
Proof. exact (eq_refl (term139 A t x)). Qed.
Lemma lem3786357 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term627 A t x x' f s) = (term623 A t x x' f s).
Proof. exact (MK_COMB (@lem3786356 A t x) (@lem3786355 A x' f s)). Qed.
Lemma lem3786358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786359 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term629 A t x x' f s) = (term630 A t x x' f s).
Proof. exact (MK_COMB (@lem3786358) (@lem3786357 A t x x' f s)). Qed.
Lemma lem3786360 {A : Type'} (x' : A -> Prop) (f : type686 A) (t : type1402 A) (s : A -> Prop) : (term389 A x' f s t) = (term368 A x' f t s).
Proof. exact (eq_refl (term389 A x' f s t)). Qed.
Lemma lem3786361 {A : Type'} (t : type686 A) (x : A -> Prop) : (term139 A t x) = (term139 A t x).
Proof. exact (eq_refl (term139 A t x)). Qed.
Lemma lem3786362 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term631 A t x x' f s t') = (term632 A t x x' f t' s).
Proof. exact (MK_COMB (@lem3786361 A t x) (@lem3786360 A x' f t' s)). Qed.
Lemma lem3786363 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term633 A t x x' f s) = (term634 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786362 A t x x' f t' s)). Qed.
Lemma lem3786364 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786365 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term628 A t x x' f s) = (term635 A t x x' f s).
Proof. exact (MK_COMB (@lem3786364 A) (@lem3786363 A t x x' f s)). Qed.
Lemma lem3786366 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term627 A t x x' f s) = (term628 A t x x' f s)) = ((term623 A t x x' f s) = (term635 A t x x' f s)).
Proof. exact (MK_COMB (@lem3786359 A t x x' f s) (@lem3786365 A t x x' f s)). Qed.
Lemma lem3786367 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term623 A t x x' f s) = (term635 A t x x' f s).
Proof. exact (EQ_MP (@lem3786366 A t x x' f s) (@lem3786351 A t x x' f s)). Qed.
Lemma lem3786368 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term625 A t x f s) = (term636 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786367 A t x x' f s)). Qed.
Lemma lem3786369 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786370 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term626 A t x f s) = (term637 A t x f s).
Proof. exact (MK_COMB (@lem3786369 A) (@lem3786368 A t x f s)). Qed.
Lemma lem3786371 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term619 A t x f s) = (term637 A t x f s).
Proof. exact (TRANS (@lem3786347 A t x f s) (@lem3786370 A t x f s)). Qed.
Lemma lem3786372 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term638 A t f s) = (term639 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786371 A t x f s)). Qed.
Lemma lem3786373 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786374 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term616 A t f s) = (term640 A t f s).
Proof. exact (MK_COMB (@lem3786373 A) (@lem3786372 A t f s)). Qed.
Lemma lem3786375 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term615 A t f s) = (term640 A t f s).
Proof. exact (TRANS (@lem3786327 A t f s) (@lem3786374 A t f s)). Qed.
Lemma lem3786376 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term610 A t f s) = (term640 A t f s).
Proof. exact (TRANS (@lem3786323 A t f s) (@lem3786375 A t f s)). Qed.
Lemma lem3786377 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786378 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term611 A t f s) = (term641 A t f s).
Proof. exact (MK_COMB (@lem3786377 A t) (@lem3786376 A t f s)). Qed.
Lemma lem3786380 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786381 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786380 (A -> Prop) P Q). Qed.
Lemma lem3786382 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term642 A t f s) = (term643 A t f s).
Proof. exact (@lem3786381 A (@FINITE (A -> Prop) t) (term639 A t f s)). Qed.
Lemma lem3786383 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term644 A t f s x) = (term637 A t x f s).
Proof. exact (eq_refl (term644 A t f s x)). Qed.
Lemma lem3786384 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term645 A t f s) = (term639 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786383 A t x f s)). Qed.
Lemma lem3786385 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786386 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term646 A t f s) = (term640 A t f s).
Proof. exact (MK_COMB (@lem3786385 A) (@lem3786384 A t f s)). Qed.
Lemma lem3786387 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786388 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term642 A t f s) = (term641 A t f s).
Proof. exact (MK_COMB (@lem3786387 A t) (@lem3786386 A t f s)). Qed.
Lemma lem3786389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786390 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term647 A t f s) = (term648 A t f s).
Proof. exact (MK_COMB (@lem3786389) (@lem3786388 A t f s)). Qed.
Lemma lem3786391 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term644 A t f s x) = (term637 A t x f s).
Proof. exact (eq_refl (term644 A t f s x)). Qed.
Lemma lem3786392 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786393 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term649 A t f s x) = (term650 A t x f s).
Proof. exact (MK_COMB (@lem3786392 A t) (@lem3786391 A t x f s)). Qed.
Lemma lem3786394 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term651 A t f s) = (term652 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786393 A t x f s)). Qed.
Lemma lem3786395 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786396 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term643 A t f s) = (term653 A t f s).
Proof. exact (MK_COMB (@lem3786395 A) (@lem3786394 A t f s)). Qed.
Lemma lem3786397 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : ((term642 A t f s) = (term643 A t f s)) = ((term641 A t f s) = (term653 A t f s)).
Proof. exact (MK_COMB (@lem3786390 A t f s) (@lem3786396 A t f s)). Qed.
Lemma lem3786398 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term641 A t f s) = (term653 A t f s).
Proof. exact (EQ_MP (@lem3786397 A t f s) (@lem3786382 A t f s)). Qed.
Lemma lem3786400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786401 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786400 (A -> Prop) P Q). Qed.
Lemma lem3786402 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term654 A t x f s) = (term655 A t x f s).
Proof. exact (@lem3786401 A (@FINITE (A -> Prop) t) (term636 A t x f s)). Qed.
Lemma lem3786403 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term656 A t x f s x') = (term635 A t x x' f s).
Proof. exact (eq_refl (term656 A t x f s x')). Qed.
Lemma lem3786404 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term657 A t x f s) = (term636 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786403 A t x x' f s)). Qed.
Lemma lem3786405 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786406 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term658 A t x f s) = (term637 A t x f s).
Proof. exact (MK_COMB (@lem3786405 A) (@lem3786404 A t x f s)). Qed.
Lemma lem3786407 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786408 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term654 A t x f s) = (term650 A t x f s).
Proof. exact (MK_COMB (@lem3786407 A t) (@lem3786406 A t x f s)). Qed.
Lemma lem3786409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786410 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term659 A t x f s) = (term660 A t x f s).
Proof. exact (MK_COMB (@lem3786409) (@lem3786408 A t x f s)). Qed.
Lemma lem3786411 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term656 A t x f s x') = (term635 A t x x' f s).
Proof. exact (eq_refl (term656 A t x f s x')). Qed.
Lemma lem3786412 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786413 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term661 A t x f s x') = (term662 A t x x' f s).
Proof. exact (MK_COMB (@lem3786412 A t) (@lem3786411 A t x x' f s)). Qed.
Lemma lem3786414 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term663 A t x f s) = (term664 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786413 A t x x' f s)). Qed.
Lemma lem3786415 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786416 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term655 A t x f s) = (term665 A t x f s).
Proof. exact (MK_COMB (@lem3786415 A) (@lem3786414 A t x f s)). Qed.
Lemma lem3786417 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term654 A t x f s) = (term655 A t x f s)) = ((term650 A t x f s) = (term665 A t x f s)).
Proof. exact (MK_COMB (@lem3786410 A t x f s) (@lem3786416 A t x f s)). Qed.
Lemma lem3786418 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term650 A t x f s) = (term665 A t x f s).
Proof. exact (EQ_MP (@lem3786417 A t x f s) (@lem3786402 A t x f s)). Qed.
Lemma lem3786420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786421 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786420 (type1402 A) P Q). Qed.
Lemma lem3786422 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term666 A t x x' f s) = (term667 A t x x' f s).
Proof. exact (@lem3786421 A (@FINITE (A -> Prop) t) (term634 A t x x' f s)). Qed.
Lemma lem3786423 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term668 A t x x' f s t') = (term632 A t x x' f t' s).
Proof. exact (eq_refl (term668 A t x x' f s t')). Qed.
Lemma lem3786424 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term669 A t x x' f s) = (term634 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786423 A t x x' f t' s)). Qed.
Lemma lem3786425 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786426 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term670 A t x x' f s) = (term635 A t x x' f s).
Proof. exact (MK_COMB (@lem3786425 A) (@lem3786424 A t x x' f s)). Qed.
Lemma lem3786427 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786428 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term666 A t x x' f s) = (term662 A t x x' f s).
Proof. exact (MK_COMB (@lem3786427 A t) (@lem3786426 A t x x' f s)). Qed.
Lemma lem3786429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786430 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term671 A t x x' f s) = (term672 A t x x' f s).
Proof. exact (MK_COMB (@lem3786429) (@lem3786428 A t x x' f s)). Qed.
Lemma lem3786431 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term668 A t x x' f s t') = (term632 A t x x' f t' s).
Proof. exact (eq_refl (term668 A t x x' f s t')). Qed.
Lemma lem3786432 {A : Type'} (t : type686 A) : (term66 A t) = (term66 A t).
Proof. exact (eq_refl (term66 A t)). Qed.
Lemma lem3786433 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term673 A t x x' f s t') = (term674 A t x x' f t' s).
Proof. exact (MK_COMB (@lem3786432 A t) (@lem3786431 A t x x' f t' s)). Qed.
Lemma lem3786434 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term675 A t x x' f s) = (term676 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786433 A t x x' f t' s)). Qed.
Lemma lem3786435 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786436 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term667 A t x x' f s) = (term677 A t x x' f s).
Proof. exact (MK_COMB (@lem3786435 A) (@lem3786434 A t x x' f s)). Qed.
Lemma lem3786437 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term666 A t x x' f s) = (term667 A t x x' f s)) = ((term662 A t x x' f s) = (term677 A t x x' f s)).
Proof. exact (MK_COMB (@lem3786430 A t x x' f s) (@lem3786436 A t x x' f s)). Qed.
Lemma lem3786438 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term662 A t x x' f s) = (term677 A t x x' f s).
Proof. exact (EQ_MP (@lem3786437 A t x x' f s) (@lem3786422 A t x x' f s)). Qed.
Lemma lem3786439 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term664 A t x f s) = (term678 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786438 A t x x' f s)). Qed.
Lemma lem3786440 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786441 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term665 A t x f s) = (term679 A t x f s).
Proof. exact (MK_COMB (@lem3786440 A) (@lem3786439 A t x f s)). Qed.
Lemma lem3786442 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term650 A t x f s) = (term679 A t x f s).
Proof. exact (TRANS (@lem3786418 A t x f s) (@lem3786441 A t x f s)). Qed.
Lemma lem3786443 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term652 A t f s) = (term680 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786442 A t x f s)). Qed.
Lemma lem3786444 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786445 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term653 A t f s) = (term681 A t f s).
Proof. exact (MK_COMB (@lem3786444 A) (@lem3786443 A t f s)). Qed.
Lemma lem3786446 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term641 A t f s) = (term681 A t f s).
Proof. exact (TRANS (@lem3786398 A t f s) (@lem3786445 A t f s)). Qed.
Lemma lem3786447 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term611 A t f s) = (term681 A t f s).
Proof. exact (TRANS (@lem3786378 A t f s) (@lem3786446 A t f s)). Qed.
Lemma lem3786448 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786449 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term613 A t f s) = (term682 A t f s).
Proof. exact (MK_COMB (@lem3786448 A t f) (@lem3786447 A t f s)). Qed.
Lemma lem3786451 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786452 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786451 (A -> Prop) P Q). Qed.
Lemma lem3786453 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term683 A t f s) = (term684 A t f s).
Proof. exact (@lem3786452 A (term609 A t f) (term680 A t f s)). Qed.
Lemma lem3786454 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term685 A t f s x) = (term679 A t x f s).
Proof. exact (eq_refl (term685 A t f s x)). Qed.
Lemma lem3786455 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term686 A t f s) = (term680 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786454 A t x f s)). Qed.
Lemma lem3786456 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786457 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term687 A t f s) = (term681 A t f s).
Proof. exact (MK_COMB (@lem3786456 A) (@lem3786455 A t f s)). Qed.
Lemma lem3786458 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786459 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term683 A t f s) = (term682 A t f s).
Proof. exact (MK_COMB (@lem3786458 A t f) (@lem3786457 A t f s)). Qed.
Lemma lem3786460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786461 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term688 A t f s) = (term689 A t f s).
Proof. exact (MK_COMB (@lem3786460) (@lem3786459 A t f s)). Qed.
Lemma lem3786462 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term685 A t f s x) = (term679 A t x f s).
Proof. exact (eq_refl (term685 A t f s x)). Qed.
Lemma lem3786463 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786464 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term690 A t f s x) = (term691 A t x f s).
Proof. exact (MK_COMB (@lem3786463 A t f) (@lem3786462 A t x f s)). Qed.
Lemma lem3786465 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term692 A t f s) = (term693 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786464 A t x f s)). Qed.
Lemma lem3786466 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786467 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term684 A t f s) = (term694 A t f s).
Proof. exact (MK_COMB (@lem3786466 A) (@lem3786465 A t f s)). Qed.
Lemma lem3786468 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : ((term683 A t f s) = (term684 A t f s)) = ((term682 A t f s) = (term694 A t f s)).
Proof. exact (MK_COMB (@lem3786461 A t f s) (@lem3786467 A t f s)). Qed.
Lemma lem3786469 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term682 A t f s) = (term694 A t f s).
Proof. exact (EQ_MP (@lem3786468 A t f s) (@lem3786453 A t f s)). Qed.
Lemma lem3786471 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786472 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786471 (A -> Prop) P Q). Qed.
Lemma lem3786473 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term695 A t x f s) = (term696 A t x f s).
Proof. exact (@lem3786472 A (term609 A t f) (term678 A t x f s)). Qed.
Lemma lem3786474 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term697 A t x f s x') = (term677 A t x x' f s).
Proof. exact (eq_refl (term697 A t x f s x')). Qed.
Lemma lem3786475 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term698 A t x f s) = (term678 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786474 A t x x' f s)). Qed.
Lemma lem3786476 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786477 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term699 A t x f s) = (term679 A t x f s).
Proof. exact (MK_COMB (@lem3786476 A) (@lem3786475 A t x f s)). Qed.
Lemma lem3786478 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786479 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term695 A t x f s) = (term691 A t x f s).
Proof. exact (MK_COMB (@lem3786478 A t f) (@lem3786477 A t x f s)). Qed.
Lemma lem3786480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786481 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term700 A t x f s) = (term701 A t x f s).
Proof. exact (MK_COMB (@lem3786480) (@lem3786479 A t x f s)). Qed.
Lemma lem3786482 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term697 A t x f s x') = (term677 A t x x' f s).
Proof. exact (eq_refl (term697 A t x f s x')). Qed.
Lemma lem3786483 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786484 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term702 A t x f s x') = (term703 A t x x' f s).
Proof. exact (MK_COMB (@lem3786483 A t f) (@lem3786482 A t x x' f s)). Qed.
Lemma lem3786485 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term704 A t x f s) = (term705 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786484 A t x x' f s)). Qed.
Lemma lem3786486 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786487 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term696 A t x f s) = (term706 A t x f s).
Proof. exact (MK_COMB (@lem3786486 A) (@lem3786485 A t x f s)). Qed.
Lemma lem3786488 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term695 A t x f s) = (term696 A t x f s)) = ((term691 A t x f s) = (term706 A t x f s)).
Proof. exact (MK_COMB (@lem3786481 A t x f s) (@lem3786487 A t x f s)). Qed.
Lemma lem3786489 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term691 A t x f s) = (term706 A t x f s).
Proof. exact (EQ_MP (@lem3786488 A t x f s) (@lem3786473 A t x f s)). Qed.
Lemma lem3786491 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786492 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786491 (type1402 A) P Q). Qed.
Lemma lem3786493 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term707 A t x x' f s) = (term708 A t x x' f s).
Proof. exact (@lem3786492 A (term609 A t f) (term676 A t x x' f s)). Qed.
Lemma lem3786494 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term709 A t x x' f s t') = (term674 A t x x' f t' s).
Proof. exact (eq_refl (term709 A t x x' f s t')). Qed.
Lemma lem3786495 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term710 A t x x' f s) = (term676 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786494 A t x x' f t' s)). Qed.
Lemma lem3786496 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786497 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term711 A t x x' f s) = (term677 A t x x' f s).
Proof. exact (MK_COMB (@lem3786496 A) (@lem3786495 A t x x' f s)). Qed.
Lemma lem3786498 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786499 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term707 A t x x' f s) = (term703 A t x x' f s).
Proof. exact (MK_COMB (@lem3786498 A t f) (@lem3786497 A t x x' f s)). Qed.
Lemma lem3786500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786501 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term712 A t x x' f s) = (term713 A t x x' f s).
Proof. exact (MK_COMB (@lem3786500) (@lem3786499 A t x x' f s)). Qed.
Lemma lem3786502 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term709 A t x x' f s t') = (term674 A t x x' f t' s).
Proof. exact (eq_refl (term709 A t x x' f s t')). Qed.
Lemma lem3786503 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term612 A t f).
Proof. exact (eq_refl (term612 A t f)). Qed.
Lemma lem3786504 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term714 A t x x' f s t') = (term715 A t x x' f t' s).
Proof. exact (MK_COMB (@lem3786503 A t f) (@lem3786502 A t x x' f t' s)). Qed.
Lemma lem3786505 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term716 A t x x' f s) = (term717 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786504 A t x x' f t' s)). Qed.
Lemma lem3786506 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786507 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term708 A t x x' f s) = (term718 A t x x' f s).
Proof. exact (MK_COMB (@lem3786506 A) (@lem3786505 A t x x' f s)). Qed.
Lemma lem3786508 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term707 A t x x' f s) = (term708 A t x x' f s)) = ((term703 A t x x' f s) = (term718 A t x x' f s)).
Proof. exact (MK_COMB (@lem3786501 A t x x' f s) (@lem3786507 A t x x' f s)). Qed.
Lemma lem3786509 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term703 A t x x' f s) = (term718 A t x x' f s).
Proof. exact (EQ_MP (@lem3786508 A t x x' f s) (@lem3786493 A t x x' f s)). Qed.
Lemma lem3786510 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term705 A t x f s) = (term719 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786509 A t x x' f s)). Qed.
Lemma lem3786511 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786512 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term706 A t x f s) = (term720 A t x f s).
Proof. exact (MK_COMB (@lem3786511 A) (@lem3786510 A t x f s)). Qed.
Lemma lem3786513 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term691 A t x f s) = (term720 A t x f s).
Proof. exact (TRANS (@lem3786489 A t x f s) (@lem3786512 A t x f s)). Qed.
Lemma lem3786514 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term693 A t f s) = (term721 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786513 A t x f s)). Qed.
Lemma lem3786515 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786516 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term694 A t f s) = (term722 A t f s).
Proof. exact (MK_COMB (@lem3786515 A) (@lem3786514 A t f s)). Qed.
Lemma lem3786517 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term682 A t f s) = (term722 A t f s).
Proof. exact (TRANS (@lem3786469 A t f s) (@lem3786516 A t f s)). Qed.
Lemma lem3786518 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term613 A t f s) = (term722 A t f s).
Proof. exact (TRANS (@lem3786449 A t f s) (@lem3786517 A t f s)). Qed.
Lemma lem3786519 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term614 A t f s) = (term723 A t f s).
Proof. exact (MK_COMB (@lem3786160 A s t) (@lem3786518 A t f s)). Qed.
Lemma lem3786521 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3786522 {A : Type'} (P : type421 A) (Q : Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (@lem3786521 (type1402 A) P Q). Qed.
Lemma lem3786523 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term724 A t f s) = (term725 A t f s).
Proof. exact (@lem3786522 A (term298 A s t) (term722 A t f s)). Qed.
Lemma lem3786524 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term308 A s t t') = (term296 A s t t').
Proof. exact (eq_refl (term308 A s t t')). Qed.
Lemma lem3786525 {A : Type'} (s : A -> Prop) (t : type686 A) : (term309 A s t) = (term298 A s t).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786524 A s t t')). Qed.
Lemma lem3786526 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786527 {A : Type'} (s : A -> Prop) (t : type686 A) : (term310 A s t) = (term299 A s t).
Proof. exact (MK_COMB (@lem3786526 A) (@lem3786525 A s t)). Qed.
Lemma lem3786528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786529 {A : Type'} (s : A -> Prop) (t : type686 A) : (term311 A s t) = (term300 A s t).
Proof. exact (MK_COMB (@lem3786528) (@lem3786527 A s t)). Qed.
Lemma lem3786530 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term722 A t f s) = (term722 A t f s).
Proof. exact (eq_refl (term722 A t f s)). Qed.
Lemma lem3786531 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term724 A t f s) = (term723 A t f s).
Proof. exact (MK_COMB (@lem3786529 A s t) (@lem3786530 A t f s)). Qed.
Lemma lem3786532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786533 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term726 A t f s) = (term727 A t f s).
Proof. exact (MK_COMB (@lem3786532) (@lem3786531 A t f s)). Qed.
Lemma lem3786534 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term308 A s t t') = (term296 A s t t').
Proof. exact (eq_refl (term308 A s t t')). Qed.
Lemma lem3786535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786536 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term314 A s t t') = (term315 A s t t').
Proof. exact (MK_COMB (@lem3786535) (@lem3786534 A s t t')). Qed.
Lemma lem3786537 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term722 A t f s) = (term722 A t f s).
Proof. exact (eq_refl (term722 A t f s)). Qed.
Lemma lem3786538 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term728 A t t' f s) = (term729 A t t' f s).
Proof. exact (MK_COMB (@lem3786536 A s t' t) (@lem3786537 A t' f s)). Qed.
Lemma lem3786539 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term730 A t f s) = (term731 A t f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786538 A t' t f s)). Qed.
Lemma lem3786540 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786541 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term725 A t f s) = (term732 A t f s).
Proof. exact (MK_COMB (@lem3786540 A) (@lem3786539 A t f s)). Qed.
Lemma lem3786542 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : ((term724 A t f s) = (term725 A t f s)) = ((term723 A t f s) = (term732 A t f s)).
Proof. exact (MK_COMB (@lem3786533 A t f s) (@lem3786541 A t f s)). Qed.
Lemma lem3786543 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term723 A t f s) = (term732 A t f s).
Proof. exact (EQ_MP (@lem3786542 A t f s) (@lem3786523 A t f s)). Qed.
Lemma lem3786545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786546 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786545 (A -> Prop) P Q). Qed.
Lemma lem3786547 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term733 A t t' f s) = (term734 A t t' f s).
Proof. exact (@lem3786546 A (term296 A s t' t) (term721 A t' f s)). Qed.
Lemma lem3786548 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term735 A t f s x) = (term720 A t x f s).
Proof. exact (eq_refl (term735 A t f s x)). Qed.
Lemma lem3786549 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term736 A t f s) = (term721 A t f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786548 A t x f s)). Qed.
Lemma lem3786550 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786551 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term737 A t f s) = (term722 A t f s).
Proof. exact (MK_COMB (@lem3786550 A) (@lem3786549 A t f s)). Qed.
Lemma lem3786552 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786553 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term733 A t t' f s) = (term729 A t t' f s).
Proof. exact (MK_COMB (@lem3786552 A s t' t) (@lem3786551 A t' f s)). Qed.
Lemma lem3786554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786555 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term738 A t t' f s) = (term739 A t t' f s).
Proof. exact (MK_COMB (@lem3786554) (@lem3786553 A t t' f s)). Qed.
Lemma lem3786556 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term735 A t f s x) = (term720 A t x f s).
Proof. exact (eq_refl (term735 A t f s x)). Qed.
Lemma lem3786557 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786558 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term740 A t t' f s x) = (term741 A t t' x f s).
Proof. exact (MK_COMB (@lem3786557 A s t' t) (@lem3786556 A t' x f s)). Qed.
Lemma lem3786559 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term742 A t t' f s) = (term743 A t t' f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786558 A t t' x f s)). Qed.
Lemma lem3786560 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786561 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term734 A t t' f s) = (term744 A t t' f s).
Proof. exact (MK_COMB (@lem3786560 A) (@lem3786559 A t t' f s)). Qed.
Lemma lem3786562 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : ((term733 A t t' f s) = (term734 A t t' f s)) = ((term729 A t t' f s) = (term744 A t t' f s)).
Proof. exact (MK_COMB (@lem3786555 A t t' f s) (@lem3786561 A t t' f s)). Qed.
Lemma lem3786563 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term729 A t t' f s) = (term744 A t t' f s).
Proof. exact (EQ_MP (@lem3786562 A t t' f s) (@lem3786547 A t t' f s)). Qed.
Lemma lem3786565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786566 {A : Type'} (P : Prop) (Q : type686 A) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem3786565 (A -> Prop) P Q). Qed.
Lemma lem3786567 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term745 A t t' x f s) = (term746 A t t' x f s).
Proof. exact (@lem3786566 A (term296 A s t' t) (term719 A t' x f s)). Qed.
Lemma lem3786568 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term747 A t x f s x') = (term718 A t x x' f s).
Proof. exact (eq_refl (term747 A t x f s x')). Qed.
Lemma lem3786569 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term748 A t x f s) = (term719 A t x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786568 A t x x' f s)). Qed.
Lemma lem3786570 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786571 {A : Type'} (t : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term749 A t x f s) = (term720 A t x f s).
Proof. exact (MK_COMB (@lem3786570 A) (@lem3786569 A t x f s)). Qed.
Lemma lem3786572 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786573 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term745 A t t' x f s) = (term741 A t t' x f s).
Proof. exact (MK_COMB (@lem3786572 A s t' t) (@lem3786571 A t' x f s)). Qed.
Lemma lem3786574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786575 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term750 A t t' x f s) = (term751 A t t' x f s).
Proof. exact (MK_COMB (@lem3786574) (@lem3786573 A t t' x f s)). Qed.
Lemma lem3786576 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term747 A t x f s x') = (term718 A t x x' f s).
Proof. exact (eq_refl (term747 A t x f s x')). Qed.
Lemma lem3786577 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786578 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term752 A t t' x f s x') = (term753 A t t' x x' f s).
Proof. exact (MK_COMB (@lem3786577 A s t' t) (@lem3786576 A t' x x' f s)). Qed.
Lemma lem3786579 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term754 A t t' x f s) = (term755 A t t' x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786578 A t t' x x' f s)). Qed.
Lemma lem3786580 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786581 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term746 A t t' x f s) = (term756 A t t' x f s).
Proof. exact (MK_COMB (@lem3786580 A) (@lem3786579 A t t' x f s)). Qed.
Lemma lem3786582 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term745 A t t' x f s) = (term746 A t t' x f s)) = ((term741 A t t' x f s) = (term756 A t t' x f s)).
Proof. exact (MK_COMB (@lem3786575 A t t' x f s) (@lem3786581 A t t' x f s)). Qed.
Lemma lem3786583 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term741 A t t' x f s) = (term756 A t t' x f s).
Proof. exact (EQ_MP (@lem3786582 A t t' x f s) (@lem3786567 A t t' x f s)). Qed.
Lemma lem3786585 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786586 {A : Type'} (P : Prop) (Q : type421 A) : (term327 A P Q) = (term328 A P Q).
Proof. exact (@lem3786585 (type1402 A) P Q). Qed.
Lemma lem3786587 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term757 A t t' x x' f s) = (term758 A t t' x x' f s).
Proof. exact (@lem3786586 A (term296 A s t' t) (term717 A t' x x' f s)). Qed.
Lemma lem3786588 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term759 A t x x' f s t') = (term715 A t x x' f t' s).
Proof. exact (eq_refl (term759 A t x x' f s t')). Qed.
Lemma lem3786589 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term760 A t x x' f s) = (term717 A t x x' f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786588 A t x x' f t' s)). Qed.
Lemma lem3786590 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786591 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term761 A t x x' f s) = (term718 A t x x' f s).
Proof. exact (MK_COMB (@lem3786590 A) (@lem3786589 A t x x' f s)). Qed.
Lemma lem3786592 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786593 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term757 A t t' x x' f s) = (term753 A t t' x x' f s).
Proof. exact (MK_COMB (@lem3786592 A s t' t) (@lem3786591 A t' x x' f s)). Qed.
Lemma lem3786594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786595 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term762 A t t' x x' f s) = (term763 A t t' x x' f s).
Proof. exact (MK_COMB (@lem3786594) (@lem3786593 A t t' x x' f s)). Qed.
Lemma lem3786596 {A : Type'} (t : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t' : type1402 A) (s : A -> Prop) : (term759 A t x x' f s t') = (term715 A t x x' f t' s).
Proof. exact (eq_refl (term759 A t x x' f s t')). Qed.
Lemma lem3786597 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : type1402 A) : (term315 A s t t') = (term315 A s t t').
Proof. exact (eq_refl (term315 A s t t')). Qed.
Lemma lem3786598 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (t'' : type1402 A) (s : A -> Prop) : (term764 A t t' x x' f s t'') = (term765 A t t' x x' f t'' s).
Proof. exact (MK_COMB (@lem3786597 A s t' t) (@lem3786596 A t' x x' f t'' s)). Qed.
Lemma lem3786599 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term766 A t t' x x' f s) = (term767 A t t' x x' f s).
Proof. exact (fun_ext (fun t'' : type1402 A => @lem3786598 A t t' x x' f t'' s)). Qed.
Lemma lem3786600 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786601 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term758 A t t' x x' f s) = (term768 A t t' x x' f s).
Proof. exact (MK_COMB (@lem3786600 A) (@lem3786599 A t t' x x' f s)). Qed.
Lemma lem3786602 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : ((term757 A t t' x x' f s) = (term758 A t t' x x' f s)) = ((term753 A t t' x x' f s) = (term768 A t t' x x' f s)).
Proof. exact (MK_COMB (@lem3786595 A t t' x x' f s) (@lem3786601 A t t' x x' f s)). Qed.
Lemma lem3786603 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (x' : A -> Prop) (f : type686 A) (s : A -> Prop) : (term753 A t t' x x' f s) = (term768 A t t' x x' f s).
Proof. exact (EQ_MP (@lem3786602 A t t' x x' f s) (@lem3786587 A t t' x x' f s)). Qed.
Lemma lem3786604 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term755 A t t' x f s) = (term769 A t t' x f s).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3786603 A t t' x x' f s)). Qed.
Lemma lem3786605 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786606 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term756 A t t' x f s) = (term770 A t t' x f s).
Proof. exact (MK_COMB (@lem3786605 A) (@lem3786604 A t t' x f s)). Qed.
Lemma lem3786607 {A : Type'} (t : type1402 A) (t' : type686 A) (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term741 A t t' x f s) = (term770 A t t' x f s).
Proof. exact (TRANS (@lem3786583 A t t' x f s) (@lem3786606 A t t' x f s)). Qed.
Lemma lem3786608 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term743 A t t' f s) = (term771 A t t' f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786607 A t t' x f s)). Qed.
Lemma lem3786609 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786610 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term744 A t t' f s) = (term772 A t t' f s).
Proof. exact (MK_COMB (@lem3786609 A) (@lem3786608 A t t' f s)). Qed.
Lemma lem3786611 {A : Type'} (t : type1402 A) (t' : type686 A) (f : type686 A) (s : A -> Prop) : (term729 A t t' f s) = (term772 A t t' f s).
Proof. exact (TRANS (@lem3786563 A t t' f s) (@lem3786610 A t t' f s)). Qed.
Lemma lem3786612 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term731 A t f s) = (term773 A t f s).
Proof. exact (fun_ext (fun t' : type1402 A => @lem3786611 A t' t f s)). Qed.
Lemma lem3786613 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3786614 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term732 A t f s) = (term774 A t f s).
Proof. exact (MK_COMB (@lem3786613 A) (@lem3786612 A t f s)). Qed.
Lemma lem3786615 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term723 A t f s) = (term774 A t f s).
Proof. exact (TRANS (@lem3786543 A t f s) (@lem3786614 A t f s)). Qed.
Lemma lem3786617 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term614 A t f s) = (term774 A t f s).
Proof. exact (TRANS (@lem3786519 A t f s) (@lem3786615 A t f s)). Qed.
Lemma lem3786618 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) : (term582 A t f s) = (term774 A t f s).
Proof. exact (TRANS (@lem3785795 A t f s) (@lem3786617 A t f s)). Qed.
Lemma lem3786619 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term582 A t f s) : term774 A t f s.
Proof. exact (EQ_MP (@lem3786618 A t f s) (@lem3785656 A t f s h1)). Qed.
Lemma lem3786621 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term134 A t x).
Proof. exact (eq_refl (term134 A t x)). Qed.
Lemma lem3786622 {A : Type'} (t : type686 A) : (term136 A t) = (term136 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3786621 A t x)). Qed.
Lemma lem3786623 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3786624 {A : Type'} (t : type686 A) : (term137 A t) = (term137 A t).
Proof. exact (MK_COMB (@lem3786623 A) (@lem3786622 A t)). Qed.
Lemma lem3786625 {A : Type'} (t : type686 A) : (term775 A t) = (term137 A t).
Proof. exact (@lem16933 (term137 A t)). Qed.
Lemma lem3786626 {A : Type'} (t : type686 A) : (term775 A t) = (term137 A t).
Proof. exact (TRANS (@lem3786625 A t) (@lem3786624 A t)). Qed.
Lemma lem3786638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term401 A s t x) = (term402 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3786639 {A : Type'} (P : A -> Prop) : (term403 A P) = (term404 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3786640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term406 A s t).
Proof. exact (@lem3786639 A (term148 A s t)). Qed.
Lemma lem3786641 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term407 A s t x) = (term146 A s t x).
Proof. exact (eq_refl (term407 A s t x)). Qed.
Lemma lem3786642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3786643 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term408 A s t x) = (term401 A s t x).
Proof. exact (MK_COMB (@lem3786642) (@lem3786641 A s t x)). Qed.
Lemma lem3786644 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term408 A s t x) = (term402 A s t x).
Proof. exact (TRANS (@lem3786643 A s t x) (@lem3786638 A s t x)). Qed.
Lemma lem3786645 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term409 A s t) = (term410 A s t).
Proof. exact (fun_ext (fun x : A => @lem3786644 A s t x)). Qed.
Lemma lem3786646 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term406 A s t) = (term411 A s t).
Proof. exact (MK_COMB (@lem3786646 A) (@lem3786645 A s t)). Qed.
Lemma lem3786648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term411 A s t).
Proof. exact (TRANS (@lem3786640 A s t) (@lem3786647 A s t)). Qed.
Lemma lem3786655 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term401 A t s x) = (term402 A t s x).
Proof. exact (@lem17362 (t x) (s x)). Qed.
Lemma lem3786656 {A : Type'} (P : A -> Prop) : (term403 A P) = (term404 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3786657 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term405 A t s) = (term406 A t s).
Proof. exact (@lem3786656 A (term148 A t s)). Qed.
Lemma lem3786658 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term407 A t s x) = (term146 A t s x).
Proof. exact (eq_refl (term407 A t s x)). Qed.
Lemma lem3786659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3786660 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term408 A t s x) = (term401 A t s x).
Proof. exact (MK_COMB (@lem3786659) (@lem3786658 A t s x)). Qed.
Lemma lem3786661 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term408 A t s x) = (term402 A t s x).
Proof. exact (TRANS (@lem3786660 A t s x) (@lem3786655 A t s x)). Qed.
Lemma lem3786662 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term409 A t s) = (term410 A t s).
Proof. exact (fun_ext (fun x : A => @lem3786661 A t s x)). Qed.
Lemma lem3786663 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786664 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term406 A t s) = (term411 A t s).
Proof. exact (MK_COMB (@lem3786663 A) (@lem3786662 A t s)). Qed.
Lemma lem3786665 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term405 A t s) = (term411 A t s).
Proof. exact (TRANS (@lem3786657 A t s) (@lem3786664 A t s)). Qed.
Lemma lem3786666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786667 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term776 A s t) = (term777 A s t).
Proof. exact (MK_COMB (@lem3786666) (@lem3786648 A s t)). Qed.
Lemma lem3786668 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term778 A t s) = (term779 A t s).
Proof. exact (MK_COMB (@lem3786667 A s t) (@lem3786665 A t s)). Qed.
Lemma lem3786669 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term780 A t s) = (term778 A t s).
Proof. exact (@lem17160 (term149 A s t) (term149 A t s)). Qed.
Lemma lem3786670 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term780 A t s) = (term779 A t s).
Proof. exact (TRANS (@lem3786669 A t s) (@lem3786668 A t s)). Qed.
Lemma lem3786672 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786673 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term782 A t t' s) = (term783 A t t' s).
Proof. exact (MK_COMB (@lem3786672 A s t t') (@lem3786670 A t' s)). Qed.
Lemma lem3786674 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term784 A t t' s) = (term782 A t t' s).
Proof. exact (@lem17362 (term141 A s t t') (term151 A t' s)). Qed.
Lemma lem3786675 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term784 A t t' s) = (term783 A t t' s).
Proof. exact (TRANS (@lem3786674 A t t' s) (@lem3786673 A t t' s)). Qed.
Lemma lem3786676 {A : Type'} (P : type686 A) : (term238 A P) = (term239 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3786677 {A : Type'} (t : type686 A) (s : A -> Prop) : (term785 A t s) = (term786 A t s).
Proof. exact (@lem3786676 A (term153 A t s)). Qed.
Lemma lem3786678 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term787 A t s t') = (term152 A t t' s).
Proof. exact (eq_refl (term787 A t s t')). Qed.
Lemma lem3786679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3786680 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term788 A t s t') = (term784 A t t' s).
Proof. exact (MK_COMB (@lem3786679) (@lem3786678 A t t' s)). Qed.
Lemma lem3786681 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term788 A t s t') = (term783 A t t' s).
Proof. exact (TRANS (@lem3786680 A t t' s) (@lem3786675 A t t' s)). Qed.
Lemma lem3786682 {A : Type'} (t : type686 A) (s : A -> Prop) : (term789 A t s) = (term790 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786681 A t t' s)). Qed.
Lemma lem3786683 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786684 {A : Type'} (t : type686 A) (s : A -> Prop) : (term786 A t s) = (term791 A t s).
Proof. exact (MK_COMB (@lem3786683 A) (@lem3786682 A t s)). Qed.
Lemma lem3786685 {A : Type'} (t : type686 A) (s : A -> Prop) : (term785 A t s) = (term791 A t s).
Proof. exact (TRANS (@lem3786677 A t s) (@lem3786684 A t s)). Qed.
Lemma lem3786686 {A : Type'} (P : type686 A) : (term238 A P) = (term239 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3786687 {A : Type'} (t : type686 A) : (term792 A t) = (term793 A t).
Proof. exact (@lem3786686 A (term155 A t)). Qed.
Lemma lem3786688 {A : Type'} (t : type686 A) (s : A -> Prop) : (term794 A t s) = (term154 A t s).
Proof. exact (eq_refl (term794 A t s)). Qed.
Lemma lem3786689 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3786690 {A : Type'} (t : type686 A) (s : A -> Prop) : (term795 A t s) = (term785 A t s).
Proof. exact (MK_COMB (@lem3786689) (@lem3786688 A t s)). Qed.
Lemma lem3786691 {A : Type'} (t : type686 A) (s : A -> Prop) : (term795 A t s) = (term791 A t s).
Proof. exact (TRANS (@lem3786690 A t s) (@lem3786685 A t s)). Qed.
Lemma lem3786692 {A : Type'} (t : type686 A) : (term796 A t) = (term797 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3786691 A t s)). Qed.
Lemma lem3786693 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786694 {A : Type'} (t : type686 A) : (term793 A t) = (term798 A t).
Proof. exact (MK_COMB (@lem3786693 A) (@lem3786692 A t)). Qed.
Lemma lem3786695 {A : Type'} (t : type686 A) : (term792 A t) = (term798 A t).
Proof. exact (TRANS (@lem3786687 A t) (@lem3786694 A t)). Qed.
Lemma lem3786696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3786697 {A : Type'} (t : type686 A) : (term799 A t) = (term800 A t).
Proof. exact (MK_COMB (@lem3786696) (@lem3786626 A t)). Qed.
Lemma lem3786698 {A : Type'} (t : type686 A) : (term801 A t) = (term802 A t).
Proof. exact (MK_COMB (@lem3786697 A t) (@lem3786695 A t)). Qed.
Lemma lem3786699 {A : Type'} (t : type686 A) : (term803 A t) = (term801 A t).
Proof. exact (@lem17045 (term158 A t) (term156 A t)). Qed.
Lemma lem3786700 {A : Type'} (t : type686 A) : (term803 A t) = (term802 A t).
Proof. exact (TRANS (@lem3786699 A t) (@lem3786698 A t)). Qed.
Lemma lem3786702 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3786703 {A : Type'} (t : type686 A) : (term805 A t) = (term806 A t).
Proof. exact (MK_COMB (@lem3786702 A t) (@lem3786700 A t)). Qed.
Lemma lem3786704 {A : Type'} (t : type686 A) : (term606 A t) = (term805 A t).
Proof. exact (@lem17045 (@FINITE (A -> Prop) t) (term584 A t)). Qed.
Lemma lem3786705 {A : Type'} (t : type686 A) : (term606 A t) = (term806 A t).
Proof. exact (TRANS (@lem3786704 A t) (@lem3786703 A t)). Qed.
Lemma lem3786820 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3786821 {A : Type'} (P : A -> Prop) (Q : Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (@lem3786820 A P Q). Qed.
Lemma lem3786822 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term807 A t s) = (term808 A t s).
Proof. exact (@lem3786821 A (term410 A s t) (term411 A t s)). Qed.
Lemma lem3786823 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term425 A s t x) = (term402 A s t x).
Proof. exact (eq_refl (term425 A s t x)). Qed.
Lemma lem3786824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term426 A s t) = (term410 A s t).
Proof. exact (fun_ext (fun x : A => @lem3786823 A s t x)). Qed.
Lemma lem3786825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786826 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term427 A s t) = (term411 A s t).
Proof. exact (MK_COMB (@lem3786825 A) (@lem3786824 A s t)). Qed.
Lemma lem3786827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786828 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term809 A s t) = (term777 A s t).
Proof. exact (MK_COMB (@lem3786827) (@lem3786826 A s t)). Qed.
Lemma lem3786829 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term411 A t s) = (term411 A t s).
Proof. exact (eq_refl (term411 A t s)). Qed.
Lemma lem3786830 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term807 A t s) = (term779 A t s).
Proof. exact (MK_COMB (@lem3786828 A s t) (@lem3786829 A t s)). Qed.
Lemma lem3786831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786832 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term810 A t s) = (term811 A t s).
Proof. exact (MK_COMB (@lem3786831) (@lem3786830 A t s)). Qed.
Lemma lem3786833 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term425 A s t x) = (term402 A s t x).
Proof. exact (eq_refl (term425 A s t x)). Qed.
Lemma lem3786834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3786835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term812 A s t x) = (term813 A s t x).
Proof. exact (MK_COMB (@lem3786834) (@lem3786833 A s t x)). Qed.
Lemma lem3786836 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term411 A t s) = (term411 A t s).
Proof. exact (eq_refl (term411 A t s)). Qed.
Lemma lem3786837 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term814 A x t s) = (term815 A x t s).
Proof. exact (MK_COMB (@lem3786835 A s t x) (@lem3786836 A t s)). Qed.
Lemma lem3786838 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term816 A t s) = (term817 A t s).
Proof. exact (fun_ext (fun x : A => @lem3786837 A x t s)). Qed.
Lemma lem3786839 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786840 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term808 A t s) = (term818 A t s).
Proof. exact (MK_COMB (@lem3786839 A) (@lem3786838 A t s)). Qed.
Lemma lem3786841 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term807 A t s) = (term808 A t s)) = ((term779 A t s) = (term818 A t s)).
Proof. exact (MK_COMB (@lem3786832 A t s) (@lem3786840 A t s)). Qed.
Lemma lem3786842 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term779 A t s) = (term818 A t s).
Proof. exact (EQ_MP (@lem3786841 A t s) (@lem3786822 A t s)). Qed.
Lemma lem3786844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (@lem3786844 A P Q). Qed.
Lemma lem3786846 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term819 A x t s) = (term820 A x t s).
Proof. exact (@lem3786845 A (term402 A s t x) (term410 A t s)). Qed.
Lemma lem3786847 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term425 A t s x) = (term402 A t s x).
Proof. exact (eq_refl (term425 A t s x)). Qed.
Lemma lem3786848 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term426 A t s) = (term410 A t s).
Proof. exact (fun_ext (fun x : A => @lem3786847 A t s x)). Qed.
Lemma lem3786849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786850 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term427 A t s) = (term411 A t s).
Proof. exact (MK_COMB (@lem3786849 A) (@lem3786848 A t s)). Qed.
Lemma lem3786851 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term813 A s t x) = (term813 A s t x).
Proof. exact (eq_refl (term813 A s t x)). Qed.
Lemma lem3786852 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term819 A x t s) = (term815 A x t s).
Proof. exact (MK_COMB (@lem3786851 A s t x) (@lem3786850 A t s)). Qed.
Lemma lem3786853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786854 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term821 A x t s) = (term822 A x t s).
Proof. exact (MK_COMB (@lem3786853) (@lem3786852 A x t s)). Qed.
Lemma lem3786855 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term425 A t s x') = (term402 A t s x').
Proof. exact (eq_refl (term425 A t s x')). Qed.
Lemma lem3786856 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term813 A s t x) = (term813 A s t x).
Proof. exact (eq_refl (term813 A s t x)). Qed.
Lemma lem3786857 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term823 A x t s x') = (term824 A x t s x').
Proof. exact (MK_COMB (@lem3786856 A s t x) (@lem3786855 A t s x')). Qed.
Lemma lem3786858 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term825 A x t s) = (term826 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3786857 A x t s x')). Qed.
Lemma lem3786859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786860 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term820 A x t s) = (term827 A x t s).
Proof. exact (MK_COMB (@lem3786859 A) (@lem3786858 A x t s)). Qed.
Lemma lem3786861 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term819 A x t s) = (term820 A x t s)) = ((term815 A x t s) = (term827 A x t s)).
Proof. exact (MK_COMB (@lem3786854 A x t s) (@lem3786860 A x t s)). Qed.
Lemma lem3786862 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term815 A x t s) = (term827 A x t s).
Proof. exact (EQ_MP (@lem3786861 A x t s) (@lem3786846 A x t s)). Qed.
Lemma lem3786863 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term817 A t s) = (term828 A t s).
Proof. exact (fun_ext (fun x : A => @lem3786862 A x t s)). Qed.
Lemma lem3786864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786865 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term818 A t s) = (term829 A t s).
Proof. exact (MK_COMB (@lem3786864 A) (@lem3786863 A t s)). Qed.
Lemma lem3786866 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term779 A t s) = (term829 A t s).
Proof. exact (TRANS (@lem3786842 A t s) (@lem3786865 A t s)). Qed.
Lemma lem3786867 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786868 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term783 A t t' s) = (term830 A t t' s).
Proof. exact (MK_COMB (@lem3786867 A s t t') (@lem3786866 A t' s)). Qed.
Lemma lem3786870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (@lem3786870 A P Q). Qed.
Lemma lem3786872 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term831 A t t' s) = (term832 A t t' s).
Proof. exact (@lem3786871 A (term141 A s t t') (term828 A t' s)). Qed.
Lemma lem3786873 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term833 A t s x) = (term827 A x t s).
Proof. exact (eq_refl (term833 A t s x)). Qed.
Lemma lem3786874 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term834 A t s) = (term828 A t s).
Proof. exact (fun_ext (fun x : A => @lem3786873 A x t s)). Qed.
Lemma lem3786875 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786876 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term835 A t s) = (term829 A t s).
Proof. exact (MK_COMB (@lem3786875 A) (@lem3786874 A t s)). Qed.
Lemma lem3786877 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786878 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term831 A t t' s) = (term830 A t t' s).
Proof. exact (MK_COMB (@lem3786877 A s t t') (@lem3786876 A t' s)). Qed.
Lemma lem3786879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786880 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term836 A t t' s) = (term837 A t t' s).
Proof. exact (MK_COMB (@lem3786879) (@lem3786878 A t t' s)). Qed.
Lemma lem3786881 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term833 A t s x) = (term827 A x t s).
Proof. exact (eq_refl (term833 A t s x)). Qed.
Lemma lem3786882 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786883 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term838 A t t' s x) = (term839 A t x t' s).
Proof. exact (MK_COMB (@lem3786882 A s t t') (@lem3786881 A x t' s)). Qed.
Lemma lem3786884 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term840 A t t' s) = (term841 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3786883 A t x t' s)). Qed.
Lemma lem3786885 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786886 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term832 A t t' s) = (term842 A t t' s).
Proof. exact (MK_COMB (@lem3786885 A) (@lem3786884 A t t' s)). Qed.
Lemma lem3786887 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : ((term831 A t t' s) = (term832 A t t' s)) = ((term830 A t t' s) = (term842 A t t' s)).
Proof. exact (MK_COMB (@lem3786880 A t t' s) (@lem3786886 A t t' s)). Qed.
Lemma lem3786888 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term830 A t t' s) = (term842 A t t' s).
Proof. exact (EQ_MP (@lem3786887 A t t' s) (@lem3786872 A t t' s)). Qed.
Lemma lem3786890 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3786891 {A : Type'} (P : Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (@lem3786890 A P Q). Qed.
Lemma lem3786892 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term843 A t x t' s) = (term844 A t x t' s).
Proof. exact (@lem3786891 A (term141 A s t t') (term826 A x t' s)). Qed.
Lemma lem3786893 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term845 A x t s x') = (term824 A x t s x').
Proof. exact (eq_refl (term845 A x t s x')). Qed.
Lemma lem3786894 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term846 A x t s) = (term826 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3786893 A x t s x')). Qed.
Lemma lem3786895 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786896 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term847 A x t s) = (term827 A x t s).
Proof. exact (MK_COMB (@lem3786895 A) (@lem3786894 A x t s)). Qed.
Lemma lem3786897 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786898 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term843 A t x t' s) = (term839 A t x t' s).
Proof. exact (MK_COMB (@lem3786897 A s t t') (@lem3786896 A x t' s)). Qed.
Lemma lem3786899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786900 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term848 A t x t' s) = (term849 A t x t' s).
Proof. exact (MK_COMB (@lem3786899) (@lem3786898 A t x t' s)). Qed.
Lemma lem3786901 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term845 A x t s x') = (term824 A x t s x').
Proof. exact (eq_refl (term845 A x t s x')). Qed.
Lemma lem3786902 {A : Type'} (s : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s t t') = (term781 A s t t').
Proof. exact (eq_refl (term781 A s t t')). Qed.
Lemma lem3786903 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term850 A t x t' s x') = (term851 A t x t' s x').
Proof. exact (MK_COMB (@lem3786902 A s t t') (@lem3786901 A x t' s x')). Qed.
Lemma lem3786904 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term852 A t x t' s) = (term853 A t x t' s).
Proof. exact (fun_ext (fun x' : A => @lem3786903 A t x t' s x')). Qed.
Lemma lem3786905 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786906 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term844 A t x t' s) = (term854 A t x t' s).
Proof. exact (MK_COMB (@lem3786905 A) (@lem3786904 A t x t' s)). Qed.
Lemma lem3786907 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : ((term843 A t x t' s) = (term844 A t x t' s)) = ((term839 A t x t' s) = (term854 A t x t' s)).
Proof. exact (MK_COMB (@lem3786900 A t x t' s) (@lem3786906 A t x t' s)). Qed.
Lemma lem3786908 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term839 A t x t' s) = (term854 A t x t' s).
Proof. exact (EQ_MP (@lem3786907 A t x t' s) (@lem3786892 A t x t' s)). Qed.
Lemma lem3786909 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term841 A t t' s) = (term855 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3786908 A t x t' s)). Qed.
Lemma lem3786910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786911 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term842 A t t' s) = (term856 A t t' s).
Proof. exact (MK_COMB (@lem3786910 A) (@lem3786909 A t t' s)). Qed.
Lemma lem3786912 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term830 A t t' s) = (term856 A t t' s).
Proof. exact (TRANS (@lem3786888 A t t' s) (@lem3786911 A t t' s)). Qed.
Lemma lem3786913 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term783 A t t' s) = (term856 A t t' s).
Proof. exact (TRANS (@lem3786868 A t t' s) (@lem3786912 A t t' s)). Qed.
Lemma lem3786914 {A : Type'} (t : type686 A) (s : A -> Prop) : (term790 A t s) = (term857 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786913 A t t' s)). Qed.
Lemma lem3786915 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786916 {A : Type'} (t : type686 A) (s : A -> Prop) : (term791 A t s) = (term858 A t s).
Proof. exact (MK_COMB (@lem3786915 A) (@lem3786914 A t s)). Qed.
Lemma lem3786917 {A : Type'} (t : type686 A) : (term797 A t) = (term859 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3786916 A t s)). Qed.
Lemma lem3786918 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786919 {A : Type'} (t : type686 A) : (term798 A t) = (term860 A t).
Proof. exact (MK_COMB (@lem3786918 A) (@lem3786917 A t)). Qed.
Lemma lem3786920 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786921 {A : Type'} (t : type686 A) : (term802 A t) = (term861 A t).
Proof. exact (MK_COMB (@lem3786920 A t) (@lem3786919 A t)). Qed.
Lemma lem3786923 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786924 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3786923 (A -> Prop) P Q). Qed.
Lemma lem3786925 {A : Type'} (t : type686 A) : (term862 A t) = (term863 A t).
Proof. exact (@lem3786924 A (term137 A t) (term859 A t)). Qed.
Lemma lem3786926 {A : Type'} (t : type686 A) (s : A -> Prop) : (term864 A t s) = (term858 A t s).
Proof. exact (eq_refl (term864 A t s)). Qed.
Lemma lem3786927 {A : Type'} (t : type686 A) : (term865 A t) = (term859 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3786926 A t s)). Qed.
Lemma lem3786928 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786929 {A : Type'} (t : type686 A) : (term866 A t) = (term860 A t).
Proof. exact (MK_COMB (@lem3786928 A) (@lem3786927 A t)). Qed.
Lemma lem3786930 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786931 {A : Type'} (t : type686 A) : (term862 A t) = (term861 A t).
Proof. exact (MK_COMB (@lem3786930 A t) (@lem3786929 A t)). Qed.
Lemma lem3786932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786933 {A : Type'} (t : type686 A) : (term867 A t) = (term868 A t).
Proof. exact (MK_COMB (@lem3786932) (@lem3786931 A t)). Qed.
Lemma lem3786934 {A : Type'} (t : type686 A) (s : A -> Prop) : (term864 A t s) = (term858 A t s).
Proof. exact (eq_refl (term864 A t s)). Qed.
Lemma lem3786935 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786936 {A : Type'} (t : type686 A) (s : A -> Prop) : (term869 A t s) = (term870 A t s).
Proof. exact (MK_COMB (@lem3786935 A t) (@lem3786934 A t s)). Qed.
Lemma lem3786937 {A : Type'} (t : type686 A) : (term871 A t) = (term872 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3786936 A t s)). Qed.
Lemma lem3786938 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786939 {A : Type'} (t : type686 A) : (term863 A t) = (term873 A t).
Proof. exact (MK_COMB (@lem3786938 A) (@lem3786937 A t)). Qed.
Lemma lem3786940 {A : Type'} (t : type686 A) : ((term862 A t) = (term863 A t)) = ((term861 A t) = (term873 A t)).
Proof. exact (MK_COMB (@lem3786933 A t) (@lem3786939 A t)). Qed.
Lemma lem3786941 {A : Type'} (t : type686 A) : (term861 A t) = (term873 A t).
Proof. exact (EQ_MP (@lem3786940 A t) (@lem3786925 A t)). Qed.
Lemma lem3786943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786944 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3786943 (A -> Prop) P Q). Qed.
Lemma lem3786945 {A : Type'} (t : type686 A) (s : A -> Prop) : (term874 A t s) = (term875 A t s).
Proof. exact (@lem3786944 A (term137 A t) (term857 A t s)). Qed.
Lemma lem3786946 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term876 A t s t') = (term856 A t t' s).
Proof. exact (eq_refl (term876 A t s t')). Qed.
Lemma lem3786947 {A : Type'} (t : type686 A) (s : A -> Prop) : (term877 A t s) = (term857 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786946 A t t' s)). Qed.
Lemma lem3786948 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786949 {A : Type'} (t : type686 A) (s : A -> Prop) : (term878 A t s) = (term858 A t s).
Proof. exact (MK_COMB (@lem3786948 A) (@lem3786947 A t s)). Qed.
Lemma lem3786950 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786951 {A : Type'} (t : type686 A) (s : A -> Prop) : (term874 A t s) = (term870 A t s).
Proof. exact (MK_COMB (@lem3786950 A t) (@lem3786949 A t s)). Qed.
Lemma lem3786952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786953 {A : Type'} (t : type686 A) (s : A -> Prop) : (term879 A t s) = (term880 A t s).
Proof. exact (MK_COMB (@lem3786952) (@lem3786951 A t s)). Qed.
Lemma lem3786954 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term876 A t s t') = (term856 A t t' s).
Proof. exact (eq_refl (term876 A t s t')). Qed.
Lemma lem3786955 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786956 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term881 A t s t') = (term882 A t t' s).
Proof. exact (MK_COMB (@lem3786955 A t) (@lem3786954 A t t' s)). Qed.
Lemma lem3786957 {A : Type'} (t : type686 A) (s : A -> Prop) : (term883 A t s) = (term884 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3786956 A t t' s)). Qed.
Lemma lem3786958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3786959 {A : Type'} (t : type686 A) (s : A -> Prop) : (term875 A t s) = (term885 A t s).
Proof. exact (MK_COMB (@lem3786958 A) (@lem3786957 A t s)). Qed.
Lemma lem3786960 {A : Type'} (t : type686 A) (s : A -> Prop) : ((term874 A t s) = (term875 A t s)) = ((term870 A t s) = (term885 A t s)).
Proof. exact (MK_COMB (@lem3786953 A t s) (@lem3786959 A t s)). Qed.
Lemma lem3786961 {A : Type'} (t : type686 A) (s : A -> Prop) : (term870 A t s) = (term885 A t s).
Proof. exact (EQ_MP (@lem3786960 A t s) (@lem3786945 A t s)). Qed.
Lemma lem3786963 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem3786963 A P Q). Qed.
Lemma lem3786965 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term886 A t t' s) = (term887 A t t' s).
Proof. exact (@lem3786964 A (term137 A t) (term855 A t t' s)). Qed.
Lemma lem3786966 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term888 A t t' s x) = (term854 A t x t' s).
Proof. exact (eq_refl (term888 A t t' s x)). Qed.
Lemma lem3786967 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term889 A t t' s) = (term855 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3786966 A t x t' s)). Qed.
Lemma lem3786968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786969 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term890 A t t' s) = (term856 A t t' s).
Proof. exact (MK_COMB (@lem3786968 A) (@lem3786967 A t t' s)). Qed.
Lemma lem3786970 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786971 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term886 A t t' s) = (term882 A t t' s).
Proof. exact (MK_COMB (@lem3786970 A t) (@lem3786969 A t t' s)). Qed.
Lemma lem3786972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786973 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term891 A t t' s) = (term892 A t t' s).
Proof. exact (MK_COMB (@lem3786972) (@lem3786971 A t t' s)). Qed.
Lemma lem3786974 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term888 A t t' s x) = (term854 A t x t' s).
Proof. exact (eq_refl (term888 A t t' s x)). Qed.
Lemma lem3786975 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786976 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term893 A t t' s x) = (term894 A t x t' s).
Proof. exact (MK_COMB (@lem3786975 A t) (@lem3786974 A t x t' s)). Qed.
Lemma lem3786977 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term895 A t t' s) = (term896 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3786976 A t x t' s)). Qed.
Lemma lem3786978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786979 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term887 A t t' s) = (term897 A t t' s).
Proof. exact (MK_COMB (@lem3786978 A) (@lem3786977 A t t' s)). Qed.
Lemma lem3786980 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : ((term886 A t t' s) = (term887 A t t' s)) = ((term882 A t t' s) = (term897 A t t' s)).
Proof. exact (MK_COMB (@lem3786973 A t t' s) (@lem3786979 A t t' s)). Qed.
Lemma lem3786981 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term882 A t t' s) = (term897 A t t' s).
Proof. exact (EQ_MP (@lem3786980 A t t' s) (@lem3786965 A t t' s)). Qed.
Lemma lem3786983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3786984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem3786983 A P Q). Qed.
Lemma lem3786985 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term898 A t x t' s) = (term899 A t x t' s).
Proof. exact (@lem3786984 A (term137 A t) (term853 A t x t' s)). Qed.
Lemma lem3786986 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term900 A t x t' s x') = (term851 A t x t' s x').
Proof. exact (eq_refl (term900 A t x t' s x')). Qed.
Lemma lem3786987 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term901 A t x t' s) = (term853 A t x t' s).
Proof. exact (fun_ext (fun x' : A => @lem3786986 A t x t' s x')). Qed.
Lemma lem3786988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786989 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term902 A t x t' s) = (term854 A t x t' s).
Proof. exact (MK_COMB (@lem3786988 A) (@lem3786987 A t x t' s)). Qed.
Lemma lem3786990 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786991 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term898 A t x t' s) = (term894 A t x t' s).
Proof. exact (MK_COMB (@lem3786990 A t) (@lem3786989 A t x t' s)). Qed.
Lemma lem3786992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3786993 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term903 A t x t' s) = (term904 A t x t' s).
Proof. exact (MK_COMB (@lem3786992) (@lem3786991 A t x t' s)). Qed.
Lemma lem3786994 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term900 A t x t' s x') = (term851 A t x t' s x').
Proof. exact (eq_refl (term900 A t x t' s x')). Qed.
Lemma lem3786995 {A : Type'} (t : type686 A) : (term800 A t) = (term800 A t).
Proof. exact (eq_refl (term800 A t)). Qed.
Lemma lem3786996 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term905 A t x t' s x') = (term906 A t x t' s x').
Proof. exact (MK_COMB (@lem3786995 A t) (@lem3786994 A t x t' s x')). Qed.
Lemma lem3786997 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term907 A t x t' s) = (term908 A t x t' s).
Proof. exact (fun_ext (fun x' : A => @lem3786996 A t x t' s x')). Qed.
Lemma lem3786998 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3786999 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term899 A t x t' s) = (term909 A t x t' s).
Proof. exact (MK_COMB (@lem3786998 A) (@lem3786997 A t x t' s)). Qed.
Lemma lem3787000 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : ((term898 A t x t' s) = (term899 A t x t' s)) = ((term894 A t x t' s) = (term909 A t x t' s)).
Proof. exact (MK_COMB (@lem3786993 A t x t' s) (@lem3786999 A t x t' s)). Qed.
Lemma lem3787001 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term894 A t x t' s) = (term909 A t x t' s).
Proof. exact (EQ_MP (@lem3787000 A t x t' s) (@lem3786985 A t x t' s)). Qed.
Lemma lem3787002 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term896 A t t' s) = (term910 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3787001 A t x t' s)). Qed.
Lemma lem3787003 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787004 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term897 A t t' s) = (term911 A t t' s).
Proof. exact (MK_COMB (@lem3787003 A) (@lem3787002 A t t' s)). Qed.
Lemma lem3787005 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term882 A t t' s) = (term911 A t t' s).
Proof. exact (TRANS (@lem3786981 A t t' s) (@lem3787004 A t t' s)). Qed.
Lemma lem3787006 {A : Type'} (t : type686 A) (s : A -> Prop) : (term884 A t s) = (term912 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3787005 A t t' s)). Qed.
Lemma lem3787007 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787008 {A : Type'} (t : type686 A) (s : A -> Prop) : (term885 A t s) = (term913 A t s).
Proof. exact (MK_COMB (@lem3787007 A) (@lem3787006 A t s)). Qed.
Lemma lem3787009 {A : Type'} (t : type686 A) (s : A -> Prop) : (term870 A t s) = (term913 A t s).
Proof. exact (TRANS (@lem3786961 A t s) (@lem3787008 A t s)). Qed.
Lemma lem3787010 {A : Type'} (t : type686 A) : (term872 A t) = (term914 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3787009 A t s)). Qed.
Lemma lem3787011 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787012 {A : Type'} (t : type686 A) : (term873 A t) = (term915 A t).
Proof. exact (MK_COMB (@lem3787011 A) (@lem3787010 A t)). Qed.
Lemma lem3787013 {A : Type'} (t : type686 A) : (term861 A t) = (term915 A t).
Proof. exact (TRANS (@lem3786941 A t) (@lem3787012 A t)). Qed.
Lemma lem3787014 {A : Type'} (t : type686 A) : (term802 A t) = (term915 A t).
Proof. exact (TRANS (@lem3786921 A t) (@lem3787013 A t)). Qed.
Lemma lem3787015 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787016 {A : Type'} (t : type686 A) : (term806 A t) = (term916 A t).
Proof. exact (MK_COMB (@lem3787015 A t) (@lem3787014 A t)). Qed.
Lemma lem3787018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3787019 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3787018 (A -> Prop) P Q). Qed.
Lemma lem3787020 {A : Type'} (t : type686 A) : (term917 A t) = (term918 A t).
Proof. exact (@lem3787019 A (term919 A t) (term914 A t)). Qed.
Lemma lem3787021 {A : Type'} (t : type686 A) (s : A -> Prop) : (term920 A t s) = (term913 A t s).
Proof. exact (eq_refl (term920 A t s)). Qed.
Lemma lem3787022 {A : Type'} (t : type686 A) : (term921 A t) = (term914 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3787021 A t s)). Qed.
Lemma lem3787023 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787024 {A : Type'} (t : type686 A) : (term922 A t) = (term915 A t).
Proof. exact (MK_COMB (@lem3787023 A) (@lem3787022 A t)). Qed.
Lemma lem3787025 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787026 {A : Type'} (t : type686 A) : (term917 A t) = (term916 A t).
Proof. exact (MK_COMB (@lem3787025 A t) (@lem3787024 A t)). Qed.
Lemma lem3787027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3787028 {A : Type'} (t : type686 A) : (term923 A t) = (term924 A t).
Proof. exact (MK_COMB (@lem3787027) (@lem3787026 A t)). Qed.
Lemma lem3787029 {A : Type'} (t : type686 A) (s : A -> Prop) : (term920 A t s) = (term913 A t s).
Proof. exact (eq_refl (term920 A t s)). Qed.
Lemma lem3787030 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787031 {A : Type'} (t : type686 A) (s : A -> Prop) : (term925 A t s) = (term926 A t s).
Proof. exact (MK_COMB (@lem3787030 A t) (@lem3787029 A t s)). Qed.
Lemma lem3787032 {A : Type'} (t : type686 A) : (term927 A t) = (term928 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3787031 A t s)). Qed.
Lemma lem3787033 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787034 {A : Type'} (t : type686 A) : (term918 A t) = (term929 A t).
Proof. exact (MK_COMB (@lem3787033 A) (@lem3787032 A t)). Qed.
Lemma lem3787035 {A : Type'} (t : type686 A) : ((term917 A t) = (term918 A t)) = ((term916 A t) = (term929 A t)).
Proof. exact (MK_COMB (@lem3787028 A t) (@lem3787034 A t)). Qed.
Lemma lem3787036 {A : Type'} (t : type686 A) : (term916 A t) = (term929 A t).
Proof. exact (EQ_MP (@lem3787035 A t) (@lem3787020 A t)). Qed.
Lemma lem3787038 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3787039 {A : Type'} (P : Prop) (Q : type686 A) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem3787038 (A -> Prop) P Q). Qed.
Lemma lem3787040 {A : Type'} (t : type686 A) (s : A -> Prop) : (term930 A t s) = (term931 A t s).
Proof. exact (@lem3787039 A (term919 A t) (term912 A t s)). Qed.
Lemma lem3787041 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term932 A t s t') = (term911 A t t' s).
Proof. exact (eq_refl (term932 A t s t')). Qed.
Lemma lem3787042 {A : Type'} (t : type686 A) (s : A -> Prop) : (term933 A t s) = (term912 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3787041 A t t' s)). Qed.
Lemma lem3787043 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787044 {A : Type'} (t : type686 A) (s : A -> Prop) : (term934 A t s) = (term913 A t s).
Proof. exact (MK_COMB (@lem3787043 A) (@lem3787042 A t s)). Qed.
Lemma lem3787045 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787046 {A : Type'} (t : type686 A) (s : A -> Prop) : (term930 A t s) = (term926 A t s).
Proof. exact (MK_COMB (@lem3787045 A t) (@lem3787044 A t s)). Qed.
Lemma lem3787047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3787048 {A : Type'} (t : type686 A) (s : A -> Prop) : (term935 A t s) = (term936 A t s).
Proof. exact (MK_COMB (@lem3787047) (@lem3787046 A t s)). Qed.
Lemma lem3787049 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term932 A t s t') = (term911 A t t' s).
Proof. exact (eq_refl (term932 A t s t')). Qed.
Lemma lem3787050 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787051 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term937 A t s t') = (term938 A t t' s).
Proof. exact (MK_COMB (@lem3787050 A t) (@lem3787049 A t t' s)). Qed.
Lemma lem3787052 {A : Type'} (t : type686 A) (s : A -> Prop) : (term939 A t s) = (term940 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3787051 A t t' s)). Qed.
Lemma lem3787053 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787054 {A : Type'} (t : type686 A) (s : A -> Prop) : (term931 A t s) = (term941 A t s).
Proof. exact (MK_COMB (@lem3787053 A) (@lem3787052 A t s)). Qed.
Lemma lem3787055 {A : Type'} (t : type686 A) (s : A -> Prop) : ((term930 A t s) = (term931 A t s)) = ((term926 A t s) = (term941 A t s)).
Proof. exact (MK_COMB (@lem3787048 A t s) (@lem3787054 A t s)). Qed.
Lemma lem3787056 {A : Type'} (t : type686 A) (s : A -> Prop) : (term926 A t s) = (term941 A t s).
Proof. exact (EQ_MP (@lem3787055 A t s) (@lem3787040 A t s)). Qed.
Lemma lem3787058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3787059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem3787058 A P Q). Qed.
Lemma lem3787060 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term942 A t t' s) = (term943 A t t' s).
Proof. exact (@lem3787059 A (term919 A t) (term910 A t t' s)). Qed.
Lemma lem3787061 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term944 A t t' s x) = (term909 A t x t' s).
Proof. exact (eq_refl (term944 A t t' s x)). Qed.
Lemma lem3787062 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term945 A t t' s) = (term910 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3787061 A t x t' s)). Qed.
Lemma lem3787063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787064 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term946 A t t' s) = (term911 A t t' s).
Proof. exact (MK_COMB (@lem3787063 A) (@lem3787062 A t t' s)). Qed.
Lemma lem3787065 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787066 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term942 A t t' s) = (term938 A t t' s).
Proof. exact (MK_COMB (@lem3787065 A t) (@lem3787064 A t t' s)). Qed.
Lemma lem3787067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3787068 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term947 A t t' s) = (term948 A t t' s).
Proof. exact (MK_COMB (@lem3787067) (@lem3787066 A t t' s)). Qed.
Lemma lem3787069 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term944 A t t' s x) = (term909 A t x t' s).
Proof. exact (eq_refl (term944 A t t' s x)). Qed.
Lemma lem3787070 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787071 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term949 A t t' s x) = (term950 A t x t' s).
Proof. exact (MK_COMB (@lem3787070 A t) (@lem3787069 A t x t' s)). Qed.
Lemma lem3787072 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term951 A t t' s) = (term952 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3787071 A t x t' s)). Qed.
Lemma lem3787073 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787074 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term943 A t t' s) = (term953 A t t' s).
Proof. exact (MK_COMB (@lem3787073 A) (@lem3787072 A t t' s)). Qed.
Lemma lem3787075 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : ((term942 A t t' s) = (term943 A t t' s)) = ((term938 A t t' s) = (term953 A t t' s)).
Proof. exact (MK_COMB (@lem3787068 A t t' s) (@lem3787074 A t t' s)). Qed.
Lemma lem3787076 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term938 A t t' s) = (term953 A t t' s).
Proof. exact (EQ_MP (@lem3787075 A t t' s) (@lem3787060 A t t' s)). Qed.
Lemma lem3787078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3787079 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem3787078 A P Q). Qed.
Lemma lem3787080 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term954 A t x t' s) = (term955 A t x t' s).
Proof. exact (@lem3787079 A (term919 A t) (term908 A t x t' s)). Qed.
Lemma lem3787081 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term956 A t x t' s x') = (term906 A t x t' s x').
Proof. exact (eq_refl (term956 A t x t' s x')). Qed.
Lemma lem3787082 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term957 A t x t' s) = (term908 A t x t' s).
Proof. exact (fun_ext (fun x' : A => @lem3787081 A t x t' s x')). Qed.
Lemma lem3787083 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787084 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term958 A t x t' s) = (term909 A t x t' s).
Proof. exact (MK_COMB (@lem3787083 A) (@lem3787082 A t x t' s)). Qed.
Lemma lem3787085 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787086 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term954 A t x t' s) = (term950 A t x t' s).
Proof. exact (MK_COMB (@lem3787085 A t) (@lem3787084 A t x t' s)). Qed.
Lemma lem3787087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3787088 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term959 A t x t' s) = (term960 A t x t' s).
Proof. exact (MK_COMB (@lem3787087) (@lem3787086 A t x t' s)). Qed.
Lemma lem3787089 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term956 A t x t' s x') = (term906 A t x t' s x').
Proof. exact (eq_refl (term956 A t x t' s x')). Qed.
Lemma lem3787090 {A : Type'} (t : type686 A) : (term804 A t) = (term804 A t).
Proof. exact (eq_refl (term804 A t)). Qed.
Lemma lem3787091 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) (x' : A) : (term961 A t x t' s x') = (term962 A t x t' s x').
Proof. exact (MK_COMB (@lem3787090 A t) (@lem3787089 A t x t' s x')). Qed.
Lemma lem3787092 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term963 A t x t' s) = (term964 A t x t' s).
Proof. exact (fun_ext (fun x' : A => @lem3787091 A t x t' s x')). Qed.
Lemma lem3787093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787094 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term955 A t x t' s) = (term965 A t x t' s).
Proof. exact (MK_COMB (@lem3787093 A) (@lem3787092 A t x t' s)). Qed.
Lemma lem3787095 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : ((term954 A t x t' s) = (term955 A t x t' s)) = ((term950 A t x t' s) = (term965 A t x t' s)).
Proof. exact (MK_COMB (@lem3787088 A t x t' s) (@lem3787094 A t x t' s)). Qed.
Lemma lem3787096 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s : A -> Prop) : (term950 A t x t' s) = (term965 A t x t' s).
Proof. exact (EQ_MP (@lem3787095 A t x t' s) (@lem3787080 A t x t' s)). Qed.
Lemma lem3787097 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term952 A t t' s) = (term966 A t t' s).
Proof. exact (fun_ext (fun x : A => @lem3787096 A t x t' s)). Qed.
Lemma lem3787098 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3787099 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term953 A t t' s) = (term967 A t t' s).
Proof. exact (MK_COMB (@lem3787098 A) (@lem3787097 A t t' s)). Qed.
Lemma lem3787100 {A : Type'} (t : type686 A) (t' : A -> Prop) (s : A -> Prop) : (term938 A t t' s) = (term967 A t t' s).
Proof. exact (TRANS (@lem3787076 A t t' s) (@lem3787099 A t t' s)). Qed.
Lemma lem3787101 {A : Type'} (t : type686 A) (s : A -> Prop) : (term940 A t s) = (term968 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3787100 A t t' s)). Qed.
Lemma lem3787102 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787103 {A : Type'} (t : type686 A) (s : A -> Prop) : (term941 A t s) = (term969 A t s).
Proof. exact (MK_COMB (@lem3787102 A) (@lem3787101 A t s)). Qed.
Lemma lem3787104 {A : Type'} (t : type686 A) (s : A -> Prop) : (term926 A t s) = (term969 A t s).
Proof. exact (TRANS (@lem3787056 A t s) (@lem3787103 A t s)). Qed.
Lemma lem3787105 {A : Type'} (t : type686 A) : (term928 A t) = (term970 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3787104 A t s)). Qed.
Lemma lem3787106 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3787107 {A : Type'} (t : type686 A) : (term929 A t) = (term971 A t).
Proof. exact (MK_COMB (@lem3787106 A) (@lem3787105 A t)). Qed.
Lemma lem3787108 {A : Type'} (t : type686 A) : (term916 A t) = (term971 A t).
Proof. exact (TRANS (@lem3787036 A t) (@lem3787107 A t)). Qed.
Lemma lem3787110 {A : Type'} (t : type686 A) : (term806 A t) = (term971 A t).
Proof. exact (TRANS (@lem3787016 A t) (@lem3787108 A t)). Qed.
Lemma lem3787111 {A : Type'} (t : type686 A) : (term606 A t) = (term971 A t).
Proof. exact (TRANS (@lem3786705 A t) (@lem3787110 A t)). Qed.
Lemma lem3787112 {A : Type'} (t : type686 A) (h1 : term606 A t) : term971 A t.
Proof. exact (EQ_MP (@lem3787111 A t) (@lem3785661 A t h1)). Qed.
Lemma lem3787113 {A : Type'} (t : type686 A) (s' : A -> Prop) (h1 : term969 A t s') : term969 A t s'.
Proof. exact (h1). Qed.
Lemma lem3787114 {A : Type'} (t : type686 A) (t' : A -> Prop) (s' : A -> Prop) (h1 : term967 A t t' s') : term967 A t t' s'.
Proof. exact (h1). Qed.
Lemma lem3787115 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (h1 : term965 A t x t' s') : term965 A t x t' s'.
Proof. exact (h1). Qed.
Lemma lem3787116 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term962 A t x t' s' x') : term962 A t x t' s' x'.
Proof. exact (h1). Qed.
Lemma lem3787117 {A : Type'} (t'' : type1402 A) (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term772 A t'' t f s) : term772 A t'' t f s.
Proof. exact (h1). Qed.
Lemma lem3787118 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (f : type686 A) (s : A -> Prop) (h1 : term770 A t'' t x'' f s) : term770 A t'' t x'' f s.
Proof. exact (h1). Qed.
Lemma lem3787119 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (s : A -> Prop) (h1 : term768 A t'' t x'' x''' f s) : term768 A t'' t x'' x''' f s.
Proof. exact (h1). Qed.
Lemma lem3787120 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term765 A t'' t x'' x''' f t''' s.
Proof. exact (h1). Qed.
Lemma lem3787121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787127 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787126 A Prop f x). Qed.
Lemma lem3787129 {A : Type'} (s' : A -> Prop) (x' : A) : (s' x') = (@I (A -> Prop) s' x').
Proof. exact (@lem3787127 A s' x'). Qed.
Lemma lem3787130 {A : Type'} (s' : A -> Prop) (x' : A) : (term188 A s' x') = (term460 A s' x').
Proof. exact (MK_COMB (@lem3787121) (@lem3787129 A s' x')). Qed.
Lemma lem3787135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787136 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787135 A Prop f x). Qed.
Lemma lem3787138 {A : Type'} (t' : A -> Prop) (x' : A) : (t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3787136 A t' x'). Qed.
Lemma lem3787139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787140 {A : Type'} (t' : A -> Prop) (x' : A) : (term972 A t' x') = (term973 A t' x').
Proof. exact (MK_COMB (@lem3787139) (@lem3787138 A t' x')). Qed.
Lemma lem3787141 {A : Type'} (t' : A -> Prop) (s' : A -> Prop) (x' : A) : (term402 A t' s' x') = (term974 A t' s' x').
Proof. exact (MK_COMB (@lem3787140 A t' x') (@lem3787130 A s' x')). Qed.
Lemma lem3787142 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787147 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787148 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787147 A Prop f x). Qed.
Lemma lem3787150 {A : Type'} (t' : A -> Prop) (x : A) : (t' x) = (@I (A -> Prop) t' x).
Proof. exact (@lem3787148 A t' x). Qed.
Lemma lem3787151 {A : Type'} (t' : A -> Prop) (x : A) : (term188 A t' x) = (term460 A t' x).
Proof. exact (MK_COMB (@lem3787142) (@lem3787150 A t' x)). Qed.
Lemma lem3787156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787157 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787156 A Prop f x). Qed.
Lemma lem3787159 {A : Type'} (s' : A -> Prop) (x : A) : (s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3787157 A s' x). Qed.
Lemma lem3787160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787161 {A : Type'} (s' : A -> Prop) (x : A) : (term972 A s' x) = (term973 A s' x).
Proof. exact (MK_COMB (@lem3787160) (@lem3787159 A s' x)). Qed.
Lemma lem3787162 {A : Type'} (s' : A -> Prop) (t' : A -> Prop) (x : A) : (term402 A s' t' x) = (term974 A s' t' x).
Proof. exact (MK_COMB (@lem3787161 A s' x) (@lem3787151 A t' x)). Qed.
Lemma lem3787163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787164 {A : Type'} (s' : A -> Prop) (t' : A -> Prop) (x : A) : (term813 A s' t' x) = (term975 A s' t' x).
Proof. exact (MK_COMB (@lem3787163) (@lem3787162 A s' t' x)). Qed.
Lemma lem3787165 {A : Type'} (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) : (term824 A x t' s' x') = (term976 A x t' s' x').
Proof. exact (MK_COMB (@lem3787164 A s' t' x) (@lem3787141 A t' s' x')). Qed.
Lemma lem3787170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787171 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787170 (A -> Prop) Prop f x). Qed.
Lemma lem3787173 {A : Type'} (t : type686 A) (t' : A -> Prop) : (t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem3787171 A t t'). Qed.
Lemma lem3787178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787179 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787178 (A -> Prop) Prop f x). Qed.
Lemma lem3787181 {A : Type'} (t : type686 A) (s' : A -> Prop) : (t s') = (@I ((A -> Prop) -> Prop) t s').
Proof. exact (@lem3787179 A t s'). Qed.
Lemma lem3787182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787183 {A : Type'} (t : type686 A) (s' : A -> Prop) : (term139 A t s') = (term496 A t s').
Proof. exact (MK_COMB (@lem3787182) (@lem3787181 A t s')). Qed.
Lemma lem3787184 {A : Type'} (s' : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term141 A s' t t') = (term977 A s' t t').
Proof. exact (MK_COMB (@lem3787183 A t s') (@lem3787173 A t t')). Qed.
Lemma lem3787185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787186 {A : Type'} (s' : A -> Prop) (t : type686 A) (t' : A -> Prop) : (term781 A s' t t') = (term978 A s' t t').
Proof. exact (MK_COMB (@lem3787185) (@lem3787184 A s' t t')). Qed.
Lemma lem3787187 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) : (term851 A t x t' s' x') = (term979 A t x t' s' x').
Proof. exact (MK_COMB (@lem3787186 A s' t t') (@lem3787165 A x t' s' x')). Qed.
Lemma lem3787188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787194 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787193 (A -> Prop) Prop f x). Qed.
Lemma lem3787196 {A : Type'} (t : type686 A) (x : A -> Prop) : (t x) = (@I ((A -> Prop) -> Prop) t x).
Proof. exact (@lem3787194 A t x). Qed.
Lemma lem3787197 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term477 A t x).
Proof. exact (MK_COMB (@lem3787188) (@lem3787196 A t x)). Qed.
Lemma lem3787198 {A : Type'} (t : type686 A) : (term136 A t) = (term512 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3787197 A t x)). Qed.
Lemma lem3787199 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787200 {A : Type'} (t : type686 A) : (term137 A t) = (term513 A t).
Proof. exact (MK_COMB (@lem3787199 A) (@lem3787198 A t)). Qed.
Lemma lem3787201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787202 {A : Type'} (t : type686 A) : (term800 A t) = (term980 A t).
Proof. exact (MK_COMB (@lem3787201) (@lem3787200 A t)). Qed.
Lemma lem3787203 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) : (term906 A t x t' s' x') = (term981 A t x t' s' x').
Proof. exact (MK_COMB (@lem3787202 A t) (@lem3787187 A t x t' s' x')). Qed.
Lemma lem3787204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787210 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3787209 (type686 A) Prop f x). Qed.
Lemma lem3787212 {A : Type'} (t : type686 A) : (@FINITE (A -> Prop) t) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t).
Proof. exact (@lem3787210 A (@FINITE (A -> Prop)) t). Qed.
Lemma lem3787213 {A : Type'} (t : type686 A) : (term919 A t) = (term982 A t).
Proof. exact (MK_COMB (@lem3787204) (@lem3787212 A t)). Qed.
Lemma lem3787214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787215 {A : Type'} (t : type686 A) : (term804 A t) = (term983 A t).
Proof. exact (MK_COMB (@lem3787214) (@lem3787213 A t)). Qed.
Lemma lem3787216 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) : (term962 A t x t' s' x') = (term984 A t x t' s' x').
Proof. exact (MK_COMB (@lem3787215 A t) (@lem3787203 A t x t' s' x')). Qed.
Lemma lem3787217 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term962 A t x t' s' x') : term984 A t x t' s' x'.
Proof. exact (EQ_MP (@lem3787216 A t x t' s' x') (@lem3787116 A t x t' s' x' h1)). Qed.
Lemma lem3787222 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787223 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787222 (A -> Prop) Prop f x). Qed.
Lemma lem3787225 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem3787223 A (@FINITE A) s). Qed.
Lemma lem3787232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787233 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3787232 A (A -> Prop) f x). Qed.
Lemma lem3787234 {A : Type'} (t''' : type1402 A) (x : A) : (t''' x) = (@I (A -> A -> Prop) t''' x).
Proof. exact (@lem3787233 A t''' x). Qed.
Lemma lem3787235 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3787236 {A : Type'} (t''' : type1402 A) (x : A) : (t''' x x) = (@I (A -> A -> Prop) t''' x x).
Proof. exact (MK_COMB (@lem3787234 A t''' x) (@lem3787235 A x)). Qed.
Lemma lem3787238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787239 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787238 A Prop f x). Qed.
Lemma lem3787240 {A : Type'} (t''' : type1402 A) (x : A) : (@I (A -> A -> Prop) t''' x x) = (term482 A t''' x).
Proof. exact (@lem3787239 A (@I (A -> A -> Prop) t''' x) x). Qed.
Lemma lem3787242 {A : Type'} (t''' : type1402 A) (x : A) : (t''' x x) = (term482 A t''' x).
Proof. exact (TRANS (@lem3787236 A t''' x) (@lem3787240 A t''' x)). Qed.
Lemma lem3787243 {A : Type'} (f : type686 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3787248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787249 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3787248 A (A -> Prop) f x). Qed.
Lemma lem3787251 {A : Type'} (t''' : type1402 A) (x : A) : (t''' x) = (@I (A -> A -> Prop) t''' x).
Proof. exact (@lem3787249 A t''' x). Qed.
Lemma lem3787252 {A : Type'} (f : type686 A) (t''' : type1402 A) (x : A) : (term483 A f t''' x) = (term484 A f t''' x).
Proof. exact (MK_COMB (@lem3787243 A f) (@lem3787251 A t''' x)). Qed.
Lemma lem3787254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787255 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787254 (A -> Prop) Prop f x). Qed.
Lemma lem3787256 {A : Type'} (f : type686 A) (t''' : type1402 A) (x : A) : (term484 A f t''' x) = (term485 A f t''' x).
Proof. exact (@lem3787255 A f (@I (A -> A -> Prop) t''' x)). Qed.
Lemma lem3787257 {A : Type'} (f : type686 A) (t''' : type1402 A) (x : A) : (term483 A f t''' x) = (term485 A f t''' x).
Proof. exact (TRANS (@lem3787252 A f t''' x) (@lem3787256 A f t''' x)). Qed.
Lemma lem3787258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787259 {A : Type'} (f : type686 A) (t''' : type1402 A) (x : A) : (term486 A f t''' x) = (term487 A f t''' x).
Proof. exact (MK_COMB (@lem3787258) (@lem3787257 A f t''' x)). Qed.
Lemma lem3787260 {A : Type'} (f : type686 A) (t''' : type1402 A) (x : A) : (term488 A f t''' x) = (term489 A f t''' x).
Proof. exact (MK_COMB (@lem3787259 A f t''' x) (@lem3787242 A t''' x)). Qed.
Lemma lem3787261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787266 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787267 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787266 A Prop f x). Qed.
Lemma lem3787269 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3787267 A s x). Qed.
Lemma lem3787270 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term460 A s x).
Proof. exact (MK_COMB (@lem3787261) (@lem3787269 A s x)). Qed.
Lemma lem3787271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787272 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term490 A s x).
Proof. exact (MK_COMB (@lem3787271) (@lem3787270 A s x)). Qed.
Lemma lem3787273 {A : Type'} (s : A -> Prop) (f : type686 A) (t''' : type1402 A) (x : A) : (term292 A s f t''' x) = (term491 A s f t''' x).
Proof. exact (MK_COMB (@lem3787272 A s x) (@lem3787260 A f t''' x)). Qed.
Lemma lem3787274 {A : Type'} (s : A -> Prop) (f : type686 A) (t''' : type1402 A) : (term294 A s f t''') = (term492 A s f t''').
Proof. exact (fun_ext (fun x : A => @lem3787273 A s f t''' x)). Qed.
Lemma lem3787275 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3787276 {A : Type'} (s : A -> Prop) (f : type686 A) (t''' : type1402 A) : (term296 A s f t''') = (term493 A s f t''').
Proof. exact (MK_COMB (@lem3787275 A) (@lem3787274 A s f t''')). Qed.
Lemma lem3787277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787278 {A : Type'} (s : A -> Prop) (f : type686 A) (t''' : type1402 A) : (term315 A s f t''') = (term494 A s f t''').
Proof. exact (MK_COMB (@lem3787277) (@lem3787276 A s f t''')). Qed.
Lemma lem3787279 {A : Type'} (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term317 A f t''' s) = (term495 A f t''' s).
Proof. exact (MK_COMB (@lem3787278 A s f t''') (@lem3787225 A s)). Qed.
Lemma lem3787284 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787285 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787284 (A -> Prop) Prop f x). Qed.
Lemma lem3787287 {A : Type'} (f : type686 A) (x''' : A -> Prop) : (f x''') = (@I ((A -> Prop) -> Prop) f x''').
Proof. exact (@lem3787285 A f x'''). Qed.
Lemma lem3787288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787289 {A : Type'} (f : type686 A) (x''' : A -> Prop) : (term139 A f x''') = (term496 A f x''').
Proof. exact (MK_COMB (@lem3787288) (@lem3787287 A f x''')). Qed.
Lemma lem3787290 {A : Type'} (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term338 A x''' f t''' s) = (term497 A x''' f t''' s).
Proof. exact (MK_COMB (@lem3787289 A f x''') (@lem3787279 A f t''' s)). Qed.
Lemma lem3787295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787296 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787295 A Prop f x). Qed.
Lemma lem3787298 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3787296 A t x). Qed.
Lemma lem3787299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787304 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787305 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787304 A Prop f x). Qed.
Lemma lem3787307 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3787305 A u x). Qed.
Lemma lem3787308 {A : Type'} (u : A -> Prop) (x : A) : (term188 A u x) = (term460 A u x).
Proof. exact (MK_COMB (@lem3787299) (@lem3787307 A u x)). Qed.
Lemma lem3787309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787310 {A : Type'} (u : A -> Prop) (x : A) : (term246 A u x) = (term490 A u x).
Proof. exact (MK_COMB (@lem3787309) (@lem3787308 A u x)). Qed.
Lemma lem3787311 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term224 A u t x) = (term498 A u t x).
Proof. exact (MK_COMB (@lem3787310 A u x) (@lem3787298 A t x)). Qed.
Lemma lem3787312 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term225 A u t) = (term499 A u t).
Proof. exact (fun_ext (fun x : A => @lem3787311 A u t x)). Qed.
Lemma lem3787313 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3787314 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term226 A u t) = (term500 A u t).
Proof. exact (MK_COMB (@lem3787313 A) (@lem3787312 A u t)). Qed.
Lemma lem3787319 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787320 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787319 A Prop f x). Qed.
Lemma lem3787322 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3787320 A u x). Qed.
Lemma lem3787323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787329 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787328 A Prop f x). Qed.
Lemma lem3787331 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3787329 A t x). Qed.
Lemma lem3787332 {A : Type'} (t : A -> Prop) (x : A) : (term188 A t x) = (term460 A t x).
Proof. exact (MK_COMB (@lem3787323) (@lem3787331 A t x)). Qed.
Lemma lem3787333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787334 {A : Type'} (t : A -> Prop) (x : A) : (term246 A t x) = (term490 A t x).
Proof. exact (MK_COMB (@lem3787333) (@lem3787332 A t x)). Qed.
Lemma lem3787335 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term224 A t u x) = (term498 A t u x).
Proof. exact (MK_COMB (@lem3787334 A t x) (@lem3787322 A u x)). Qed.
Lemma lem3787336 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term225 A t u) = (term499 A t u).
Proof. exact (fun_ext (fun x : A => @lem3787335 A t u x)). Qed.
Lemma lem3787337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3787338 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term226 A t u) = (term500 A t u).
Proof. exact (MK_COMB (@lem3787337 A) (@lem3787336 A t u)). Qed.
Lemma lem3787339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787340 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term227 A t u) = (term501 A t u).
Proof. exact (MK_COMB (@lem3787339) (@lem3787338 A t u)). Qed.
Lemma lem3787341 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term228 A u t) = (term502 A u t).
Proof. exact (MK_COMB (@lem3787340 A t u) (@lem3787314 A u t)). Qed.
Lemma lem3787342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787348 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787347 (A -> Prop) Prop f x). Qed.
Lemma lem3787350 {A : Type'} (f : type686 A) (u : A -> Prop) : (f u) = (@I ((A -> Prop) -> Prop) f u).
Proof. exact (@lem3787348 A f u). Qed.
Lemma lem3787351 {A : Type'} (f : type686 A) (u : A -> Prop) : (term134 A f u) = (term477 A f u).
Proof. exact (MK_COMB (@lem3787342) (@lem3787350 A f u)). Qed.
Lemma lem3787352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787358 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787357 (A -> Prop) Prop f x). Qed.
Lemma lem3787360 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3787358 A f t). Qed.
Lemma lem3787361 {A : Type'} (f : type686 A) (t : A -> Prop) : (term134 A f t) = (term477 A f t).
Proof. exact (MK_COMB (@lem3787352) (@lem3787360 A f t)). Qed.
Lemma lem3787362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787363 {A : Type'} (f : type686 A) (t : A -> Prop) : (term412 A f t) = (term478 A f t).
Proof. exact (MK_COMB (@lem3787362) (@lem3787361 A f t)). Qed.
Lemma lem3787364 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term223 A t f u) = (term503 A t f u).
Proof. exact (MK_COMB (@lem3787363 A f t) (@lem3787351 A f u)). Qed.
Lemma lem3787365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787366 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term230 A t f u) = (term504 A t f u).
Proof. exact (MK_COMB (@lem3787365) (@lem3787364 A t f u)). Qed.
Lemma lem3787367 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term232 A f u t) = (term505 A f u t).
Proof. exact (MK_COMB (@lem3787366 A t f u) (@lem3787341 A u t)). Qed.
Lemma lem3787368 {A : Type'} (f : type686 A) (t : A -> Prop) : (term233 A f t) = (term506 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3787367 A f u t)). Qed.
Lemma lem3787369 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787370 {A : Type'} (f : type686 A) (t : A -> Prop) : (term234 A f t) = (term507 A f t).
Proof. exact (MK_COMB (@lem3787369 A) (@lem3787368 A f t)). Qed.
Lemma lem3787371 {A : Type'} (f : type686 A) : (term235 A f) = (term508 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3787370 A f t)). Qed.
Lemma lem3787372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787373 {A : Type'} (f : type686 A) : (term236 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3787372 A) (@lem3787371 A f)). Qed.
Lemma lem3787374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787375 {A : Type'} (f : type686 A) : (term254 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3787374) (@lem3787373 A f)). Qed.
Lemma lem3787376 {A : Type'} (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term368 A x''' f t''' s) = (term511 A x''' f t''' s).
Proof. exact (MK_COMB (@lem3787375 A f) (@lem3787290 A x''' f t''' s)). Qed.
Lemma lem3787381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787382 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787381 (A -> Prop) Prop f x). Qed.
Lemma lem3787384 {A : Type'} (t : type686 A) (x'' : A -> Prop) : (t x'') = (@I ((A -> Prop) -> Prop) t x'').
Proof. exact (@lem3787382 A t x''). Qed.
Lemma lem3787385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787386 {A : Type'} (t : type686 A) (x'' : A -> Prop) : (term139 A t x'') = (term496 A t x'').
Proof. exact (MK_COMB (@lem3787385) (@lem3787384 A t x'')). Qed.
Lemma lem3787387 {A : Type'} (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term632 A t x'' x''' f t''' s) = (term985 A t x'' x''' f t''' s).
Proof. exact (MK_COMB (@lem3787386 A t x'') (@lem3787376 A x''' f t''' s)). Qed.
Lemma lem3787392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787393 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3787392 (type686 A) Prop f x). Qed.
Lemma lem3787395 {A : Type'} (t : type686 A) : (@FINITE (A -> Prop) t) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t).
Proof. exact (@lem3787393 A (@FINITE (A -> Prop)) t). Qed.
Lemma lem3787396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787397 {A : Type'} (t : type686 A) : (term66 A t) = (term986 A t).
Proof. exact (MK_COMB (@lem3787396) (@lem3787395 A t)). Qed.
Lemma lem3787398 {A : Type'} (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term674 A t x'' x''' f t''' s) = (term987 A t x'' x''' f t''' s).
Proof. exact (MK_COMB (@lem3787397 A t) (@lem3787387 A t x'' x''' f t''' s)). Qed.
Lemma lem3787403 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787405 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787403 (A -> Prop) Prop f x). Qed.
Lemma lem3787406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787411 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787412 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787411 (A -> Prop) Prop f x). Qed.
Lemma lem3787414 {A : Type'} (t : type686 A) (x : A -> Prop) : (t x) = (@I ((A -> Prop) -> Prop) t x).
Proof. exact (@lem3787412 A t x). Qed.
Lemma lem3787415 {A : Type'} (t : type686 A) (x : A -> Prop) : (term134 A t x) = (term477 A t x).
Proof. exact (MK_COMB (@lem3787406) (@lem3787414 A t x)). Qed.
Lemma lem3787416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787417 {A : Type'} (t : type686 A) (x : A -> Prop) : (term412 A t x) = (term478 A t x).
Proof. exact (MK_COMB (@lem3787416) (@lem3787415 A t x)). Qed.
Lemma lem3787418 {A : Type'} (t : type686 A) (f : type686 A) (x : A -> Prop) : (term607 A t f x) = (term988 A t f x).
Proof. exact (MK_COMB (@lem3787417 A t x) (@lem3787405 A f x)). Qed.
Lemma lem3787419 {A : Type'} (t : type686 A) (f : type686 A) : (term608 A t f) = (term989 A t f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3787418 A t f x)). Qed.
Lemma lem3787420 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787421 {A : Type'} (t : type686 A) (f : type686 A) : (term609 A t f) = (term990 A t f).
Proof. exact (MK_COMB (@lem3787420 A) (@lem3787419 A t f)). Qed.
Lemma lem3787422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787423 {A : Type'} (t : type686 A) (f : type686 A) : (term612 A t f) = (term991 A t f).
Proof. exact (MK_COMB (@lem3787422) (@lem3787421 A t f)). Qed.
Lemma lem3787424 {A : Type'} (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term715 A t x'' x''' f t''' s) = (term992 A t x'' x''' f t''' s).
Proof. exact (MK_COMB (@lem3787423 A t f) (@lem3787398 A t x'' x''' f t''' s)). Qed.
Lemma lem3787431 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787432 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3787431 A (A -> Prop) f x). Qed.
Lemma lem3787433 {A : Type'} (t'' : type1402 A) (x : A) : (t'' x) = (@I (A -> A -> Prop) t'' x).
Proof. exact (@lem3787432 A t'' x). Qed.
Lemma lem3787434 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3787435 {A : Type'} (t'' : type1402 A) (x : A) : (t'' x x) = (@I (A -> A -> Prop) t'' x x).
Proof. exact (MK_COMB (@lem3787433 A t'' x) (@lem3787434 A x)). Qed.
Lemma lem3787437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787438 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787437 A Prop f x). Qed.
Lemma lem3787439 {A : Type'} (t'' : type1402 A) (x : A) : (@I (A -> A -> Prop) t'' x x) = (term482 A t'' x).
Proof. exact (@lem3787438 A (@I (A -> A -> Prop) t'' x) x). Qed.
Lemma lem3787441 {A : Type'} (t'' : type1402 A) (x : A) : (t'' x x) = (term482 A t'' x).
Proof. exact (TRANS (@lem3787435 A t'' x) (@lem3787439 A t'' x)). Qed.
Lemma lem3787442 {A : Type'} (t : type686 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3787447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787448 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem3787447 A (A -> Prop) f x). Qed.
Lemma lem3787450 {A : Type'} (t'' : type1402 A) (x : A) : (t'' x) = (@I (A -> A -> Prop) t'' x).
Proof. exact (@lem3787448 A t'' x). Qed.
Lemma lem3787451 {A : Type'} (t : type686 A) (t'' : type1402 A) (x : A) : (term483 A t t'' x) = (term484 A t t'' x).
Proof. exact (MK_COMB (@lem3787442 A t) (@lem3787450 A t'' x)). Qed.
Lemma lem3787453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787454 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3787453 (A -> Prop) Prop f x). Qed.
Lemma lem3787455 {A : Type'} (t : type686 A) (t'' : type1402 A) (x : A) : (term484 A t t'' x) = (term485 A t t'' x).
Proof. exact (@lem3787454 A t (@I (A -> A -> Prop) t'' x)). Qed.
Lemma lem3787456 {A : Type'} (t : type686 A) (t'' : type1402 A) (x : A) : (term483 A t t'' x) = (term485 A t t'' x).
Proof. exact (TRANS (@lem3787451 A t t'' x) (@lem3787455 A t t'' x)). Qed.
Lemma lem3787457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787458 {A : Type'} (t : type686 A) (t'' : type1402 A) (x : A) : (term486 A t t'' x) = (term487 A t t'' x).
Proof. exact (MK_COMB (@lem3787457) (@lem3787456 A t t'' x)). Qed.
Lemma lem3787459 {A : Type'} (t : type686 A) (t'' : type1402 A) (x : A) : (term488 A t t'' x) = (term489 A t t'' x).
Proof. exact (MK_COMB (@lem3787458 A t t'' x) (@lem3787441 A t'' x)). Qed.
Lemma lem3787460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3787465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3787466 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3787465 A Prop f x). Qed.
Lemma lem3787468 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3787466 A s x). Qed.
Lemma lem3787469 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term460 A s x).
Proof. exact (MK_COMB (@lem3787460) (@lem3787468 A s x)). Qed.
Lemma lem3787470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3787471 {A : Type'} (s : A -> Prop) (x : A) : (term246 A s x) = (term490 A s x).
Proof. exact (MK_COMB (@lem3787470) (@lem3787469 A s x)). Qed.
Lemma lem3787472 {A : Type'} (s : A -> Prop) (t : type686 A) (t'' : type1402 A) (x : A) : (term292 A s t t'' x) = (term491 A s t t'' x).
Proof. exact (MK_COMB (@lem3787471 A s x) (@lem3787459 A t t'' x)). Qed.
Lemma lem3787473 {A : Type'} (s : A -> Prop) (t : type686 A) (t'' : type1402 A) : (term294 A s t t'') = (term492 A s t t'').
Proof. exact (fun_ext (fun x : A => @lem3787472 A s t t'' x)). Qed.
Lemma lem3787474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3787475 {A : Type'} (s : A -> Prop) (t : type686 A) (t'' : type1402 A) : (term296 A s t t'') = (term493 A s t t'').
Proof. exact (MK_COMB (@lem3787474 A) (@lem3787473 A s t t'')). Qed.
Lemma lem3787476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3787477 {A : Type'} (s : A -> Prop) (t : type686 A) (t'' : type1402 A) : (term315 A s t t'') = (term494 A s t t'').
Proof. exact (MK_COMB (@lem3787476) (@lem3787475 A s t t'')). Qed.
Lemma lem3787478 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) : (term765 A t'' t x'' x''' f t''' s) = (term993 A t'' t x'' x''' f t''' s).
Proof. exact (MK_COMB (@lem3787477 A s t t'') (@lem3787424 A t x'' x''' f t''' s)). Qed.
Lemma lem3787479 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term993 A t'' t x'' x''' f t''' s.
Proof. exact (EQ_MP (@lem3787478 A t'' t x'' x''' f t''' s) (@lem3787120 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787480 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term992 A t x'' x''' f t''' s.
Proof. exact (proj2 (@lem3787479 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787482 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term987 A t x'' x''' f t''' s.
Proof. exact (proj2 (@lem3787480 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787483 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term990 A t f.
Proof. exact (proj1 (@lem3787480 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787484 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term985 A t x'' x''' f t''' s.
Proof. exact (proj2 (@lem3787482 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787486 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term511 A x''' f t''' s.
Proof. exact (proj2 (@lem3787484 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787489 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term509 A f.
Proof. exact (proj1 (@lem3787486 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3787495 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term981 A t x t' s' x') : term981 A t x t' s' x'.
Proof. exact (h1). Qed.
Lemma lem3787496 {A : Type'} (t : type686 A) (h1 : term513 A t) : term513 A t.
Proof. exact (h1). Qed.
Lemma lem3787497 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term979 A t x t' s' x'.
Proof. exact (h1). Qed.
Lemma lem3787498 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term976 A x t' s' x'.
Proof. exact (proj2 (@lem3787497 A t x t' s' x' h1)). Qed.
Lemma lem3787499 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term977 A s' t t'.
Proof. exact (proj1 (@lem3787497 A t x t' s' x' h1)). Qed.
Lemma lem3787500 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term974 A t' s' x'.
Proof. exact (proj2 (@lem3787498 A t x t' s' x' h1)). Qed.
Lemma lem3787501 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term974 A s' t' x.
Proof. exact (proj1 (@lem3787498 A t x t' s' x' h1)). Qed.
Lemma lem3787732 {A : Type'} (t : type686 A) (h1 : term982 A t) : term982 A t.
Proof. exact (h1). Qed.
Lemma lem3787955 {A : Type'} (t : type686 A) (x : A -> Prop) : (term477 A t x) = (term477 A t x).
Proof. exact (eq_refl (term477 A t x)). Qed.
Lemma lem3787956 {A : Type'} (t : type686 A) : (term512 A t) = (term512 A t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3787955 A t x)). Qed.
Lemma lem3787957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787959 {A : Type'} (t : type686 A) : (term513 A t) = (term513 A t).
Proof. exact (MK_COMB (@lem3787957 A) (@lem3787956 A t)). Qed.
Lemma lem3787960 {A : Type'} (t : type686 A) (h1 : term513 A t) : term513 A t.
Proof. exact (EQ_MP (@lem3787959 A t) (@lem3787496 A t h1)). Qed.
Lemma lem3787991 {A : Type'} (t : type686 A) (f : type686 A) (x : A -> Prop) : (term988 A t f x) = (term988 A t f x).
Proof. exact (eq_refl (term988 A t f x)). Qed.
Lemma lem3787992 {A : Type'} (t : type686 A) (f : type686 A) : (term989 A t f) = (term989 A t f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3787991 A t f x)). Qed.
Lemma lem3787993 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3787995 {A : Type'} (t : type686 A) (f : type686 A) : (term990 A t f) = (term990 A t f).
Proof. exact (MK_COMB (@lem3787993 A) (@lem3787992 A t f)). Qed.
Lemma lem3787996 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term990 A t f.
Proof. exact (EQ_MP (@lem3787995 A t f) (@lem3787483 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788006 {A : Type'} (P : A -> Prop) (Q : Prop) : (term994 A P Q) = (term995 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3788007 {A : Type'} (P : A -> Prop) (Q : Prop) : (term994 A P Q) = (term995 A P Q).
Proof. exact (@lem3788006 A P Q). Qed.
Lemma lem3788008 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term996 A u t) = (term997 A u t).
Proof. exact (@lem3788007 A (term499 A t u) (term500 A u t)). Qed.
Lemma lem3788009 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term998 A t u x) = (term498 A t u x).
Proof. exact (eq_refl (term998 A t u x)). Qed.
Lemma lem3788010 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term999 A t u) = (term499 A t u).
Proof. exact (fun_ext (fun x : A => @lem3788009 A t u x)). Qed.
Lemma lem3788011 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788012 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1000 A t u) = (term500 A t u).
Proof. exact (MK_COMB (@lem3788011 A) (@lem3788010 A t u)). Qed.
Lemma lem3788013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3788014 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1001 A t u) = (term501 A t u).
Proof. exact (MK_COMB (@lem3788013) (@lem3788012 A t u)). Qed.
Lemma lem3788015 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term500 A u t) = (term500 A u t).
Proof. exact (eq_refl (term500 A u t)). Qed.
Lemma lem3788016 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term996 A u t) = (term502 A u t).
Proof. exact (MK_COMB (@lem3788014 A t u) (@lem3788015 A u t)). Qed.
Lemma lem3788017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788018 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1002 A u t) = (term1003 A u t).
Proof. exact (MK_COMB (@lem3788017) (@lem3788016 A u t)). Qed.
Lemma lem3788019 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term998 A t u x) = (term498 A t u x).
Proof. exact (eq_refl (term998 A t u x)). Qed.
Lemma lem3788020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3788021 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term1004 A t u x) = (term1005 A t u x).
Proof. exact (MK_COMB (@lem3788020) (@lem3788019 A t u x)). Qed.
Lemma lem3788022 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term500 A u t) = (term500 A u t).
Proof. exact (eq_refl (term500 A u t)). Qed.
Lemma lem3788023 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1006 A x u t) = (term1007 A x u t).
Proof. exact (MK_COMB (@lem3788021 A t u x) (@lem3788022 A u t)). Qed.
Lemma lem3788024 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1008 A u t) = (term1009 A u t).
Proof. exact (fun_ext (fun x : A => @lem3788023 A x u t)). Qed.
Lemma lem3788025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788026 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term997 A u t) = (term1010 A u t).
Proof. exact (MK_COMB (@lem3788025 A) (@lem3788024 A u t)). Qed.
Lemma lem3788027 {A : Type'} (u : A -> Prop) (t : A -> Prop) : ((term996 A u t) = (term997 A u t)) = ((term502 A u t) = (term1010 A u t)).
Proof. exact (MK_COMB (@lem3788018 A u t) (@lem3788026 A u t)). Qed.
Lemma lem3788028 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term502 A u t) = (term1010 A u t).
Proof. exact (EQ_MP (@lem3788027 A u t) (@lem3788008 A u t)). Qed.
Lemma lem3788030 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3788031 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (@lem3788030 A P Q). Qed.
Lemma lem3788032 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1013 A x u t) = (term1014 A x u t).
Proof. exact (@lem3788031 A (term498 A t u x) (term499 A u t)). Qed.
Lemma lem3788033 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term998 A u t x) = (term498 A u t x).
Proof. exact (eq_refl (term998 A u t x)). Qed.
Lemma lem3788034 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term999 A u t) = (term499 A u t).
Proof. exact (fun_ext (fun x : A => @lem3788033 A u t x)). Qed.
Lemma lem3788035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788036 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1000 A u t) = (term500 A u t).
Proof. exact (MK_COMB (@lem3788035 A) (@lem3788034 A u t)). Qed.
Lemma lem3788037 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term1005 A t u x) = (term1005 A t u x).
Proof. exact (eq_refl (term1005 A t u x)). Qed.
Lemma lem3788038 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1013 A x u t) = (term1007 A x u t).
Proof. exact (MK_COMB (@lem3788037 A t u x) (@lem3788036 A u t)). Qed.
Lemma lem3788039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788040 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1015 A x u t) = (term1016 A x u t).
Proof. exact (MK_COMB (@lem3788039) (@lem3788038 A x u t)). Qed.
Lemma lem3788041 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) : (term998 A u t x') = (term498 A u t x').
Proof. exact (eq_refl (term998 A u t x')). Qed.
Lemma lem3788042 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term1005 A t u x) = (term1005 A t u x).
Proof. exact (eq_refl (term1005 A t u x)). Qed.
Lemma lem3788043 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) : (term1017 A x u t x') = (term1018 A x u t x').
Proof. exact (MK_COMB (@lem3788042 A t u x) (@lem3788041 A u t x')). Qed.
Lemma lem3788044 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1019 A x u t) = (term1020 A x u t).
Proof. exact (fun_ext (fun x' : A => @lem3788043 A x u t x')). Qed.
Lemma lem3788045 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788046 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1014 A x u t) = (term1021 A x u t).
Proof. exact (MK_COMB (@lem3788045 A) (@lem3788044 A x u t)). Qed.
Lemma lem3788047 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : ((term1013 A x u t) = (term1014 A x u t)) = ((term1007 A x u t) = (term1021 A x u t)).
Proof. exact (MK_COMB (@lem3788040 A x u t) (@lem3788046 A x u t)). Qed.
Lemma lem3788048 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1007 A x u t) = (term1021 A x u t).
Proof. exact (EQ_MP (@lem3788047 A x u t) (@lem3788032 A x u t)). Qed.
Lemma lem3788049 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1009 A u t) = (term1022 A u t).
Proof. exact (fun_ext (fun x : A => @lem3788048 A x u t)). Qed.
Lemma lem3788050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788051 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1010 A u t) = (term1023 A u t).
Proof. exact (MK_COMB (@lem3788050 A) (@lem3788049 A u t)). Qed.
Lemma lem3788052 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term502 A u t) = (term1023 A u t).
Proof. exact (TRANS (@lem3788028 A u t) (@lem3788051 A u t)). Qed.
Lemma lem3788053 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term504 A t f u) = (term504 A t f u).
Proof. exact (eq_refl (term504 A t f u)). Qed.
Lemma lem3788054 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term505 A f u t) = (term1024 A f u t).
Proof. exact (MK_COMB (@lem3788053 A t f u) (@lem3788052 A u t)). Qed.
Lemma lem3788056 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3788057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (@lem3788056 A P Q). Qed.
Lemma lem3788058 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1025 A f u t) = (term1026 A f u t).
Proof. exact (@lem3788057 A (term503 A t f u) (term1022 A u t)). Qed.
Lemma lem3788059 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1027 A u t x) = (term1021 A x u t).
Proof. exact (eq_refl (term1027 A u t x)). Qed.
Lemma lem3788060 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1028 A u t) = (term1022 A u t).
Proof. exact (fun_ext (fun x : A => @lem3788059 A x u t)). Qed.
Lemma lem3788061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788062 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1029 A u t) = (term1023 A u t).
Proof. exact (MK_COMB (@lem3788061 A) (@lem3788060 A u t)). Qed.
Lemma lem3788063 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term504 A t f u) = (term504 A t f u).
Proof. exact (eq_refl (term504 A t f u)). Qed.
Lemma lem3788064 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1025 A f u t) = (term1024 A f u t).
Proof. exact (MK_COMB (@lem3788063 A t f u) (@lem3788062 A u t)). Qed.
Lemma lem3788065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788066 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1030 A f u t) = (term1031 A f u t).
Proof. exact (MK_COMB (@lem3788065) (@lem3788064 A f u t)). Qed.
Lemma lem3788067 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1027 A u t x) = (term1021 A x u t).
Proof. exact (eq_refl (term1027 A u t x)). Qed.
Lemma lem3788068 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term504 A t f u) = (term504 A t f u).
Proof. exact (eq_refl (term504 A t f u)). Qed.
Lemma lem3788069 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1032 A f u t x) = (term1033 A f x u t).
Proof. exact (MK_COMB (@lem3788068 A t f u) (@lem3788067 A x u t)). Qed.
Lemma lem3788070 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1034 A f u t) = (term1035 A f u t).
Proof. exact (fun_ext (fun x : A => @lem3788069 A f x u t)). Qed.
Lemma lem3788071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788072 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1026 A f u t) = (term1036 A f u t).
Proof. exact (MK_COMB (@lem3788071 A) (@lem3788070 A f u t)). Qed.
Lemma lem3788073 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : ((term1025 A f u t) = (term1026 A f u t)) = ((term1024 A f u t) = (term1036 A f u t)).
Proof. exact (MK_COMB (@lem3788066 A f u t) (@lem3788072 A f u t)). Qed.
Lemma lem3788074 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1024 A f u t) = (term1036 A f u t).
Proof. exact (EQ_MP (@lem3788073 A f u t) (@lem3788058 A f u t)). Qed.
Lemma lem3788076 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3788077 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1011 A P Q) = (term1012 A P Q).
Proof. exact (@lem3788076 A P Q). Qed.
Lemma lem3788078 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1037 A f x u t) = (term1038 A f x u t).
Proof. exact (@lem3788077 A (term503 A t f u) (term1020 A x u t)). Qed.
Lemma lem3788079 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) : (term1039 A x u t x') = (term1018 A x u t x').
Proof. exact (eq_refl (term1039 A x u t x')). Qed.
Lemma lem3788080 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1040 A x u t) = (term1020 A x u t).
Proof. exact (fun_ext (fun x' : A => @lem3788079 A x u t x')). Qed.
Lemma lem3788081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788082 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : (term1041 A x u t) = (term1021 A x u t).
Proof. exact (MK_COMB (@lem3788081 A) (@lem3788080 A x u t)). Qed.
Lemma lem3788083 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term504 A t f u) = (term504 A t f u).
Proof. exact (eq_refl (term504 A t f u)). Qed.
Lemma lem3788084 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1037 A f x u t) = (term1033 A f x u t).
Proof. exact (MK_COMB (@lem3788083 A t f u) (@lem3788082 A x u t)). Qed.
Lemma lem3788085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788086 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1042 A f x u t) = (term1043 A f x u t).
Proof. exact (MK_COMB (@lem3788085) (@lem3788084 A f x u t)). Qed.
Lemma lem3788087 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) : (term1039 A x u t x') = (term1018 A x u t x').
Proof. exact (eq_refl (term1039 A x u t x')). Qed.
Lemma lem3788088 {A : Type'} (t : A -> Prop) (f : type686 A) (u : A -> Prop) : (term504 A t f u) = (term504 A t f u).
Proof. exact (eq_refl (term504 A t f u)). Qed.
Lemma lem3788089 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) : (term1044 A f x u t x') = (term1045 A f x u t x').
Proof. exact (MK_COMB (@lem3788088 A t f u) (@lem3788087 A x u t x')). Qed.
Lemma lem3788090 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1046 A f x u t) = (term1047 A f x u t).
Proof. exact (fun_ext (fun x' : A => @lem3788089 A f x u t x')). Qed.
Lemma lem3788091 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788092 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1038 A f x u t) = (term1048 A f x u t).
Proof. exact (MK_COMB (@lem3788091 A) (@lem3788090 A f x u t)). Qed.
Lemma lem3788093 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : ((term1037 A f x u t) = (term1038 A f x u t)) = ((term1033 A f x u t) = (term1048 A f x u t)).
Proof. exact (MK_COMB (@lem3788086 A f x u t) (@lem3788092 A f x u t)). Qed.
Lemma lem3788094 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1033 A f x u t) = (term1048 A f x u t).
Proof. exact (EQ_MP (@lem3788093 A f x u t) (@lem3788078 A f x u t)). Qed.
Lemma lem3788095 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1035 A f u t) = (term1049 A f u t).
Proof. exact (fun_ext (fun x : A => @lem3788094 A f x u t)). Qed.
Lemma lem3788096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788097 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1036 A f u t) = (term1050 A f u t).
Proof. exact (MK_COMB (@lem3788096 A) (@lem3788095 A f u t)). Qed.
Lemma lem3788098 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1024 A f u t) = (term1050 A f u t).
Proof. exact (TRANS (@lem3788074 A f u t) (@lem3788097 A f u t)). Qed.
Lemma lem3788099 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term505 A f u t) = (term1050 A f u t).
Proof. exact (TRANS (@lem3788054 A f u t) (@lem3788098 A f u t)). Qed.
Lemma lem3788100 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term1051 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3788099 A f u t)). Qed.
Lemma lem3788101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3788102 {A : Type'} (f : type686 A) (t : A -> Prop) : (term507 A f t) = (term1052 A f t).
Proof. exact (MK_COMB (@lem3788101 A) (@lem3788100 A f t)). Qed.
Lemma lem3788103 {A : Type'} (f : type686 A) : (term508 A f) = (term1053 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3788102 A f t)). Qed.
Lemma lem3788104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3788105 {A : Type'} (f : type686 A) : (term509 A f) = (term1054 A f).
Proof. exact (MK_COMB (@lem3788104 A) (@lem3788103 A f)). Qed.
Lemma lem3788136 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) : (term1045 A f x u t x') = (term1045 A f x u t x').
Proof. exact (eq_refl (term1045 A f x u t x')). Qed.
Lemma lem3788137 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1047 A f x u t) = (term1047 A f x u t).
Proof. exact (fun_ext (fun x' : A => @lem3788136 A f x u t x')). Qed.
Lemma lem3788138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788139 {A : Type'} (f : type686 A) (x : A) (u : A -> Prop) (t : A -> Prop) : (term1048 A f x u t) = (term1048 A f x u t).
Proof. exact (MK_COMB (@lem3788138 A) (@lem3788137 A f x u t)). Qed.
Lemma lem3788140 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1049 A f u t) = (term1049 A f u t).
Proof. exact (fun_ext (fun x : A => @lem3788139 A f x u t)). Qed.
Lemma lem3788141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3788142 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term1050 A f u t) = (term1050 A f u t).
Proof. exact (MK_COMB (@lem3788141 A) (@lem3788140 A f u t)). Qed.
Lemma lem3788143 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1051 A f t) = (term1051 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3788142 A f u t)). Qed.
Lemma lem3788144 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3788145 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1052 A f t) = (term1052 A f t).
Proof. exact (MK_COMB (@lem3788144 A) (@lem3788143 A f t)). Qed.
Lemma lem3788146 {A : Type'} (f : type686 A) : (term1053 A f) = (term1053 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3788145 A f t)). Qed.
Lemma lem3788147 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3788148 {A : Type'} (f : type686 A) : (term1054 A f) = (term1054 A f).
Proof. exact (MK_COMB (@lem3788147 A) (@lem3788146 A f)). Qed.
Lemma lem3788149 {A : Type'} (f : type686 A) : (term509 A f) = (term1054 A f).
Proof. exact (TRANS (@lem3788105 A f) (@lem3788148 A f)). Qed.
Lemma lem3788150 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1054 A f.
Proof. exact (EQ_MP (@lem3788149 A f) (@lem3787489 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788248 {A : Type'} (_43469 : A -> Prop) (t : type686 A) (h1 : term513 A t) : term1055 A t _43469.
Proof. exact (@lem3787960 A t h1 _43469). Qed.
Lemma lem3788249 {A : Type'} (t : type686 A) (_43469 : A -> Prop) : (term1055 A t _43469) = (term477 A t _43469).
Proof. exact (eq_refl (term1055 A t _43469)). Qed.
Lemma lem3788254 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1056 A t f _43471.
Proof. exact (@lem3787996 A t'' t x'' x''' f t''' s h1 _43471). Qed.
Lemma lem3788255 {A : Type'} (t : type686 A) (f : type686 A) (_43471 : A -> Prop) : (term1056 A t f _43471) = (term988 A t f _43471).
Proof. exact (eq_refl (term1056 A t f _43471)). Qed.
Lemma lem3788257 {A : Type'} (_43472 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1057 A f _43472.
Proof. exact (@lem3788150 A t'' t x'' x''' f t''' s h1 _43472). Qed.
Lemma lem3788258 {A : Type'} (f : type686 A) (_43472 : A -> Prop) : (term1057 A f _43472) = (term1052 A f _43472).
Proof. exact (eq_refl (term1057 A f _43472)). Qed.
Lemma lem3788259 {A : Type'} (_43472 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1052 A f _43472.
Proof. exact (EQ_MP (@lem3788258 A f _43472) (@lem3788257 A _43472 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788260 {A : Type'} (_43472 : A -> Prop) (_43473 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1058 A f _43472 _43473.
Proof. exact (@lem3788259 A _43472 t'' t x'' x''' f t''' s h1 _43473). Qed.
Lemma lem3788261 {A : Type'} (f : type686 A) (_43473 : A -> Prop) (_43472 : A -> Prop) : (term1058 A f _43472 _43473) = (term1050 A f _43473 _43472).
Proof. exact (eq_refl (term1058 A f _43472 _43473)). Qed.
Lemma lem3788262 {A : Type'} (_43473 : A -> Prop) (_43472 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1050 A f _43473 _43472.
Proof. exact (EQ_MP (@lem3788261 A f _43473 _43472) (@lem3788260 A _43472 _43473 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788263 {A : Type'} (_43473 : A -> Prop) (_43472 : A -> Prop) (_43474 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1059 A f _43473 _43472 _43474.
Proof. exact (@lem3788262 A _43473 _43472 t'' t x'' x''' f t''' s h1 _43474). Qed.
Lemma lem3788264 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) : (term1059 A f _43473 _43472 _43474) = (term1048 A f _43474 _43473 _43472).
Proof. exact (eq_refl (term1059 A f _43473 _43472 _43474)). Qed.
Lemma lem3788265 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1048 A f _43474 _43473 _43472.
Proof. exact (EQ_MP (@lem3788264 A f _43474 _43473 _43472) (@lem3788263 A _43473 _43472 _43474 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788266 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1060 A f _43474 _43473 _43472 _43475.
Proof. exact (@lem3788265 A _43474 _43473 _43472 t'' t x'' x''' f t''' s h1 _43475). Qed.
Lemma lem3788267 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1060 A f _43474 _43473 _43472 _43475) = (term1045 A f _43474 _43473 _43472 _43475).
Proof. exact (eq_refl (term1060 A f _43474 _43473 _43472 _43475)). Qed.
Lemma lem3788268 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1045 A f _43474 _43473 _43472 _43475.
Proof. exact (EQ_MP (@lem3788267 A f _43474 _43473 _43472 _43475) (@lem3788266 A _43474 _43473 _43472 _43475 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788325 {A : Type'} (t : type686 A) (h1 : term982 A t) : term982 A t.
Proof. exact (h1). Qed.
Lemma lem3788391 {A : Type'} (_43469 : A -> Prop) (t : type686 A) (h1 : term513 A t) : term477 A t _43469.
Proof. exact (EQ_MP (@lem3788249 A t _43469) (@lem3788248 A _43469 t h1)). Qed.
Lemma lem3788421 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term988 A t f _43471.
Proof. exact (EQ_MP (@lem3788255 A t f _43471) (@lem3788254 A _43471 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788440 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1018 A _43474 _43473 _43472 _43475) = (term1061 A _43474 _43473 _43472 _43475).
Proof. exact (@lem3784327 (term460 A _43472 _43474) (@I (A -> Prop) _43473 _43474) (term498 A _43473 _43472 _43475)). Qed.
Lemma lem3788441 {A : Type'} (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term504 A _43472 f _43473) = (term504 A _43472 f _43473).
Proof. exact (eq_refl (term504 A _43472 f _43473)). Qed.
Lemma lem3788442 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1045 A f _43474 _43473 _43472 _43475) = (term1062 A f _43474 _43473 _43472 _43475).
Proof. exact (MK_COMB (@lem3788441 A _43472 f _43473) (@lem3788440 A _43474 _43473 _43472 _43475)). Qed.
Lemma lem3788449 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1062 A f _43474 _43473 _43472 _43475) = (term1063 A f _43474 _43473 _43472 _43475).
Proof. exact (@lem3784327 (term477 A f _43472) (term477 A f _43473) (term1061 A _43474 _43473 _43472 _43475)). Qed.
Lemma lem3788450 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1045 A f _43474 _43473 _43472 _43475) = (term1063 A f _43474 _43473 _43472 _43475).
Proof. exact (TRANS (@lem3788442 A f _43474 _43473 _43472 _43475) (@lem3788449 A f _43474 _43473 _43472 _43475)). Qed.
Lemma lem3788451 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1063 A f _43474 _43473 _43472 _43475.
Proof. exact (EQ_MP (@lem3788450 A f _43474 _43473 _43472 _43475) (@lem3788268 A _43474 _43473 _43472 _43475 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788463 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term460 A t' x.
Proof. exact (proj2 (@lem3787501 A t x t' s' x' h1)). Qed.
Lemma lem3788493 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : @I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t.
Proof. exact (proj1 (@lem3787482 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788494 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1064 A t.
Proof. exact (fun h0 : term982 A t => @lem3788493 A t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788496 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788497 {A : Type'} (t : type686 A) : (term1064 A t) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t).
Proof. exact (@lem3788496 (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t)). Qed.
Lemma lem3788498 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : @I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t.
Proof. exact (EQ_MP (@lem3788497 A t) (@lem3788494 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788501 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3788503 {A : Type'} (t : type686 A) : (term982 A t) = (term1065 A t).
Proof. exact (@lem3788501 (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) t)). Qed.
Lemma lem3788506 {A : Type'} (t : type686 A) (h1 : term982 A t) : term1065 A t.
Proof. exact (EQ_MP (@lem3788503 A t) (@lem3788325 A t h1)). Qed.
Lemma lem3788509 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (@lem3788506 A t h1 (@lem3788498 A t'' t x'' x''' f t''' s h2)). Qed.
Lemma lem3788510 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : term537.
Proof. exact (fun h0 : ~ False => @lem3788509 A t'' t x'' x''' f t''' s h1 h2). Qed.
Lemma lem3788512 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788513 : term537 = False.
Proof. exact (@lem3788512 False). Qed.
Lemma lem3788514 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3788513) (@lem3788510 A t'' t x'' x''' f t''' s h1 h2)). Qed.
Lemma lem3788516 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : @I ((A -> Prop) -> Prop) t x''.
Proof. exact (proj1 (@lem3787484 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788517 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term522 A t x''.
Proof. exact (fun h0 : term477 A t x'' => @lem3788516 A t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788519 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788520 {A : Type'} (t : type686 A) (x'' : A -> Prop) : (term522 A t x'') = (@I ((A -> Prop) -> Prop) t x'').
Proof. exact (@lem3788519 (@I ((A -> Prop) -> Prop) t x'')). Qed.
Lemma lem3788521 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : @I ((A -> Prop) -> Prop) t x''.
Proof. exact (EQ_MP (@lem3788520 A t x'') (@lem3788517 A t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788524 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3788526 {A : Type'} (t : type686 A) (_43469 : A -> Prop) : (term477 A t _43469) = (term1066 A t _43469).
Proof. exact (@lem3788524 (@I ((A -> Prop) -> Prop) t _43469)). Qed.
Lemma lem3788529 {A : Type'} (_43469 : A -> Prop) (t : type686 A) (h1 : term513 A t) : term1066 A t _43469.
Proof. exact (EQ_MP (@lem3788526 A t _43469) (@lem3788391 A _43469 t h1)). Qed.
Lemma lem3788530 {A : Type'} (_43469 : A -> Prop) (t : type686 A) (h1 : term513 A t) : term1066 A t _43469.
Proof. exact (@lem3788529 A _43469 t h1). Qed.
Lemma lem3788531 {A : Type'} (x'' : A -> Prop) (t : type686 A) (h1 : term513 A t) : term1066 A t x''.
Proof. exact (@lem3788530 A x'' t h1). Qed.
Lemma lem3788534 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term513 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (@lem3788531 A x'' t h1 (@lem3788521 A t'' t x'' x''' f t''' s h2)). Qed.
Lemma lem3788535 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term513 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : term537.
Proof. exact (fun h0 : ~ False => @lem3788534 A t'' t x'' x''' f t''' s h1 h2). Qed.
Lemma lem3788537 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788538 : term537 = False.
Proof. exact (@lem3788537 False). Qed.
Lemma lem3788539 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term513 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3788538) (@lem3788535 A t'' t x'' x''' f t''' s h1 h2)). Qed.
Lemma lem3788541 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (proj2 (@lem3787499 A t x t' s' x' h1)). Qed.
Lemma lem3788542 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term522 A t t'.
Proof. exact (fun h0 : term477 A t t' => @lem3788541 A t x t' s' x' h1). Qed.
Lemma lem3788544 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788545 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term522 A t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem3788544 (@I ((A -> Prop) -> Prop) t t')). Qed.
Lemma lem3788546 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3788545 A t t') (@lem3788542 A t x t' s' x' h1)). Qed.
Lemma lem3788552 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3788553 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : (term988 A t f _43471) = (term1067 A f t _43471).
Proof. exact (@lem3788552 (@I ((A -> Prop) -> Prop) f _43471) (term477 A t _43471)). Qed.
Lemma lem3788559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788560 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : (term1068 A t f _43471) = (term1069 A f t _43471).
Proof. exact (MK_COMB (@lem3788559) (@lem3788553 A f t _43471)). Qed.
Lemma lem3788566 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : (term1067 A f t _43471) = (term1067 A f t _43471).
Proof. exact (eq_refl (term1067 A f t _43471)). Qed.
Lemma lem3788567 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : ((term988 A t f _43471) = (term1067 A f t _43471)) = ((term1067 A f t _43471) = (term1067 A f t _43471)).
Proof. exact (MK_COMB (@lem3788560 A f t _43471) (@lem3788566 A f t _43471)). Qed.
Lemma lem3788569 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3788570 (x : Prop) : (x = x) = True.
Proof. exact (@lem3788569 Prop x). Qed.
Lemma lem3788571 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : ((term1067 A f t _43471) = (term1067 A f t _43471)) = True.
Proof. exact (@lem3788570 (term1067 A f t _43471)). Qed.
Lemma lem3788572 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : ((term988 A t f _43471) = (term1067 A f t _43471)) = True.
Proof. exact (TRANS (@lem3788567 A f t _43471) (@lem3788571 A f t _43471)). Qed.
Lemma lem3788573 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : True = ((term988 A t f _43471) = (term1067 A f t _43471)).
Proof. exact (SYM (@lem3788572 A f t _43471)). Qed.
Lemma lem3788574 {A : Type'} (f : type686 A) (t : type686 A) (_43471 : A -> Prop) : (term988 A t f _43471) = (term1067 A f t _43471).
Proof. exact (EQ_MP (@lem3788573 A f t _43471) (@lem0)). Qed.
Lemma lem3788575 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1067 A f t _43471.
Proof. exact (EQ_MP (@lem3788574 A f t _43471) (@lem3788421 A _43471 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788577 (b : Prop) (a : Prop) : (a \/ b) = (term527 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3788578 {A : Type'} (t : type686 A) (f : type686 A) (_43471 : A -> Prop) : (term1067 A f t _43471) = (term1070 A t f _43471).
Proof. exact (@lem3788577 (term477 A t _43471) (@I ((A -> Prop) -> Prop) f _43471)). Qed.
Lemma lem3788580 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3788581 {A : Type'} (t : type686 A) (_43471 : A -> Prop) : (term529 A t _43471) = (@I ((A -> Prop) -> Prop) t _43471).
Proof. exact (@lem3788580 (@I ((A -> Prop) -> Prop) t _43471)). Qed.
Lemma lem3788582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3788583 {A : Type'} (t : type686 A) (_43471 : A -> Prop) : (term530 A t _43471) = (term531 A t _43471).
Proof. exact (MK_COMB (@lem3788582) (@lem3788581 A t _43471)). Qed.
Lemma lem3788584 {A : Type'} (f : type686 A) (_43471 : A -> Prop) : (@I ((A -> Prop) -> Prop) f _43471) = (@I ((A -> Prop) -> Prop) f _43471).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) f _43471)). Qed.
Lemma lem3788585 {A : Type'} (t : type686 A) (f : type686 A) (_43471 : A -> Prop) : (term1070 A t f _43471) = (term1071 A t f _43471).
Proof. exact (MK_COMB (@lem3788583 A t _43471) (@lem3788584 A f _43471)). Qed.
Lemma lem3788586 {A : Type'} (t : type686 A) (f : type686 A) (_43471 : A -> Prop) : (term1067 A f t _43471) = (term1071 A t f _43471).
Proof. exact (TRANS (@lem3788578 A t f _43471) (@lem3788585 A t f _43471)). Qed.
Lemma lem3788589 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f _43471.
Proof. exact (EQ_MP (@lem3788586 A t f _43471) (@lem3788575 A _43471 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788590 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f _43471.
Proof. exact (@lem3788589 A _43471 t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788591 {A : Type'} (t' : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f t'.
Proof. exact (@lem3788590 A t' t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788594 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (@lem3788591 A t' t'' t x'' x''' f t''' s h1 (@lem3788546 A t x t' s' x' h2)). Qed.
Lemma lem3788595 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term522 A f t'.
Proof. exact (fun h0 : term477 A f t' => @lem3788594 A t'' x'' x''' f t''' s t x t' s' x' h1 h2). Qed.
Lemma lem3788597 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788598 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term522 A f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3788597 (@I ((A -> Prop) -> Prop) f t')). Qed.
Lemma lem3788599 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3788598 A f t') (@lem3788595 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3788601 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) t s'.
Proof. exact (proj1 (@lem3787499 A t x t' s' x' h1)). Qed.
Lemma lem3788602 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term522 A t s'.
Proof. exact (fun h0 : term477 A t s' => @lem3788601 A t x t' s' x' h1). Qed.
Lemma lem3788604 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788605 {A : Type'} (t : type686 A) (s' : A -> Prop) : (term522 A t s') = (@I ((A -> Prop) -> Prop) t s').
Proof. exact (@lem3788604 (@I ((A -> Prop) -> Prop) t s')). Qed.
Lemma lem3788606 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) t s'.
Proof. exact (EQ_MP (@lem3788605 A t s') (@lem3788602 A t x t' s' x' h1)). Qed.
Lemma lem3788608 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f _43471.
Proof. exact (EQ_MP (@lem3788586 A t f _43471) (@lem3788575 A _43471 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3788609 {A : Type'} (_43471 : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f _43471.
Proof. exact (@lem3788608 A _43471 t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788610 {A : Type'} (s' : A -> Prop) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1071 A t f s'.
Proof. exact (@lem3788609 A s' t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3788613 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) f s'.
Proof. exact (@lem3788610 A s' t'' t x'' x''' f t''' s h1 (@lem3788606 A t x t' s' x' h2)). Qed.
Lemma lem3788614 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term522 A f s'.
Proof. exact (fun h0 : term477 A f s' => @lem3788613 A t'' x'' x''' f t''' s t x t' s' x' h1 h2). Qed.
Lemma lem3788616 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788617 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term522 A f s') = (@I ((A -> Prop) -> Prop) f s').
Proof. exact (@lem3788616 (@I ((A -> Prop) -> Prop) f s')). Qed.
Lemma lem3788618 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I ((A -> Prop) -> Prop) f s'.
Proof. exact (EQ_MP (@lem3788617 A f s') (@lem3788614 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3788620 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I (A -> Prop) t' x'.
Proof. exact (proj1 (@lem3787500 A t x t' s' x' h1)). Qed.
Lemma lem3788621 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term1072 A t' x'.
Proof. exact (fun h0 : term460 A t' x' => @lem3788620 A t x t' s' x' h1). Qed.
Lemma lem3788623 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788624 {A : Type'} (t' : A -> Prop) (x' : A) : (term1072 A t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3788623 (@I (A -> Prop) t' x')). Qed.
Lemma lem3788625 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I (A -> Prop) t' x'.
Proof. exact (EQ_MP (@lem3788624 A t' x') (@lem3788621 A t x t' s' x' h1)). Qed.
Lemma lem3788627 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term460 A s' x'.
Proof. exact (proj2 (@lem3787500 A t x t' s' x' h1)). Qed.
Lemma lem3788628 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term1073 A s' x'.
Proof. exact (fun h0 : @I (A -> Prop) s' x' => @lem3788627 A t x t' s' x' h1). Qed.
Lemma lem3788630 (p : Prop) : (term1074 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3788631 {A : Type'} (s' : A -> Prop) (x' : A) : (term1073 A s' x') = (term460 A s' x').
Proof. exact (@lem3788630 (@I (A -> Prop) s' x')). Qed.
Lemma lem3788632 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term460 A s' x'.
Proof. exact (EQ_MP (@lem3788631 A s' x') (@lem3788628 A t x t' s' x' h1)). Qed.
Lemma lem3788634 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I (A -> Prop) s' x.
Proof. exact (proj1 (@lem3787501 A t x t' s' x' h1)). Qed.
Lemma lem3788635 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term1072 A s' x.
Proof. exact (fun h0 : term460 A s' x => @lem3788634 A t x t' s' x' h1). Qed.
Lemma lem3788637 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3788638 {A : Type'} (s' : A -> Prop) (x : A) : (term1072 A s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3788637 (@I (A -> Prop) s' x)). Qed.
Lemma lem3788639 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : @I (A -> Prop) s' x.
Proof. exact (EQ_MP (@lem3788638 A s' x) (@lem3788635 A t x t' s' x' h1)). Qed.
Lemma lem3788655 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788656 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1075 A f _43474 _43473 _43472 _43475) = (term1076 A f _43474 _43473 _43472 _43475).
Proof. exact (@lem3788655 (term460 A _43472 _43474) (term477 A f _43473) (term1077 A _43474 _43473 _43472 _43475)). Qed.
Lemma lem3788670 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788671 {A : Type'} (_43474 : A) (f : type686 A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1078 A f _43474 _43473 _43472 _43475) = (term1079 A _43474 f _43473 _43472 _43475).
Proof. exact (@lem3788670 (@I (A -> Prop) _43473 _43474) (term477 A f _43473) (term498 A _43473 _43472 _43475)). Qed.
Lemma lem3788685 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788686 {A : Type'} (f : type686 A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1080 A f _43473 _43472 _43475) = (term1081 A f _43473 _43472 _43475).
Proof. exact (@lem3788685 (term460 A _43473 _43475) (term477 A f _43473) (@I (A -> Prop) _43472 _43475)). Qed.
Lemma lem3788700 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3788701 {A : Type'} (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1082 A f _43473 _43472 _43475) = (term1083 A _43472 _43475 f _43473).
Proof. exact (@lem3788700 (@I (A -> Prop) _43472 _43475) (term477 A f _43473)). Qed.
Lemma lem3788707 {A : Type'} (_43473 : A -> Prop) (_43475 : A) : (term490 A _43473 _43475) = (term490 A _43473 _43475).
Proof. exact (eq_refl (term490 A _43473 _43475)). Qed.
Lemma lem3788708 {A : Type'} (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1081 A f _43473 _43472 _43475) = (term1084 A _43472 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788707 A _43473 _43475) (@lem3788701 A _43472 _43475 f _43473)). Qed.
Lemma lem3788712 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788713 {A : Type'} (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1084 A _43472 _43475 f _43473) = (term1085 A _43472 _43475 f _43473).
Proof. exact (@lem3788712 (@I (A -> Prop) _43472 _43475) (term460 A _43473 _43475) (term477 A f _43473)). Qed.
Lemma lem3788729 {A : Type'} (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1081 A f _43473 _43472 _43475) = (term1085 A _43472 _43475 f _43473).
Proof. exact (TRANS (@lem3788708 A _43472 _43475 f _43473) (@lem3788713 A _43472 _43475 f _43473)). Qed.
Lemma lem3788730 {A : Type'} (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1080 A f _43473 _43472 _43475) = (term1085 A _43472 _43475 f _43473).
Proof. exact (TRANS (@lem3788686 A f _43473 _43472 _43475) (@lem3788729 A _43472 _43475 f _43473)). Qed.
Lemma lem3788731 {A : Type'} (_43473 : A -> Prop) (_43474 : A) : (term1086 A _43473 _43474) = (term1086 A _43473 _43474).
Proof. exact (eq_refl (term1086 A _43473 _43474)). Qed.
Lemma lem3788732 {A : Type'} (_43474 : A) (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1079 A _43474 f _43473 _43472 _43475) = (term1087 A _43474 _43472 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788731 A _43473 _43474) (@lem3788730 A _43472 _43475 f _43473)). Qed.
Lemma lem3788736 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788737 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1087 A _43474 _43472 _43475 f _43473) = (term1088 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3788736 (@I (A -> Prop) _43472 _43475) (@I (A -> Prop) _43473 _43474) (term1089 A _43475 f _43473)). Qed.
Lemma lem3788763 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1079 A _43474 f _43473 _43472 _43475) = (term1088 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788732 A _43474 _43472 _43475 f _43473) (@lem3788737 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788764 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1078 A f _43474 _43473 _43472 _43475) = (term1088 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788671 A _43474 f _43473 _43472 _43475) (@lem3788763 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788765 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term490 A _43472 _43474) = (term490 A _43472 _43474).
Proof. exact (eq_refl (term490 A _43472 _43474)). Qed.
Lemma lem3788766 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1076 A f _43474 _43473 _43472 _43475) = (term1090 A _43472 _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788765 A _43472 _43474) (@lem3788764 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788770 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788771 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1090 A _43472 _43474 _43475 f _43473) = (term1091 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3788770 (@I (A -> Prop) _43472 _43475) (term460 A _43472 _43474) (term1092 A _43474 _43475 f _43473)). Qed.
Lemma lem3788785 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788786 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1093 A _43472 _43474 _43475 f _43473) = (term1094 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3788785 (@I (A -> Prop) _43473 _43474) (term460 A _43472 _43474) (term1089 A _43475 f _43473)). Qed.
Lemma lem3788812 {A : Type'} (_43472 : A -> Prop) (_43475 : A) : (term1086 A _43472 _43475) = (term1086 A _43472 _43475).
Proof. exact (eq_refl (term1086 A _43472 _43475)). Qed.
Lemma lem3788813 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1091 A _43472 _43474 _43475 f _43473) = (term1095 A _43472 _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788812 A _43472 _43475) (@lem3788786 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788824 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1090 A _43472 _43474 _43475 f _43473) = (term1095 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788771 A _43472 _43474 _43475 f _43473) (@lem3788813 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788825 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1076 A f _43474 _43473 _43472 _43475) = (term1095 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788766 A _43472 _43474 _43475 f _43473) (@lem3788824 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788826 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1075 A f _43474 _43473 _43472 _43475) = (term1095 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788656 A f _43474 _43473 _43472 _43475) (@lem3788825 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788827 {A : Type'} (f : type686 A) (_43472 : A -> Prop) : (term478 A f _43472) = (term478 A f _43472).
Proof. exact (eq_refl (term478 A f _43472)). Qed.
Lemma lem3788828 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1063 A f _43474 _43473 _43472 _43475) = (term1096 A _43472 _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788827 A f _43472) (@lem3788826 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788832 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788833 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1096 A _43472 _43474 _43475 f _43473) = (term1097 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3788832 (@I (A -> Prop) _43472 _43475) (term477 A f _43472) (term1094 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788847 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788848 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1098 A _43472 _43474 _43475 f _43473) = (term1099 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3788847 (@I (A -> Prop) _43473 _43474) (term477 A f _43472) (term1100 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3788862 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788863 {A : Type'} (_43474 : A) (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1101 A _43472 _43474 _43475 f _43473) = (term1102 A _43474 _43472 _43475 f _43473).
Proof. exact (@lem3788862 (term460 A _43472 _43474) (term477 A f _43472) (term1089 A _43475 f _43473)). Qed.
Lemma lem3788877 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788878 {A : Type'} (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1103 A _43472 _43475 f _43473) = (term1104 A _43475 _43472 f _43473).
Proof. exact (@lem3788877 (term460 A _43473 _43475) (term477 A f _43472) (term477 A f _43473)). Qed.
Lemma lem3788894 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term490 A _43472 _43474) = (term490 A _43472 _43474).
Proof. exact (eq_refl (term490 A _43472 _43474)). Qed.
Lemma lem3788895 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1102 A _43474 _43472 _43475 f _43473) = (term1105 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3788894 A _43472 _43474) (@lem3788878 A _43475 _43472 f _43473)). Qed.
Lemma lem3788906 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1101 A _43472 _43474 _43475 f _43473) = (term1105 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3788863 A _43474 _43472 _43475 f _43473) (@lem3788895 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788907 {A : Type'} (_43473 : A -> Prop) (_43474 : A) : (term1086 A _43473 _43474) = (term1086 A _43473 _43474).
Proof. exact (eq_refl (term1086 A _43473 _43474)). Qed.
Lemma lem3788908 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1099 A _43472 _43474 _43475 f _43473) = (term1106 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3788907 A _43473 _43474) (@lem3788906 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788919 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1098 A _43472 _43474 _43475 f _43473) = (term1106 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3788848 A _43472 _43474 _43475 f _43473) (@lem3788908 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788920 {A : Type'} (_43472 : A -> Prop) (_43475 : A) : (term1086 A _43472 _43475) = (term1086 A _43472 _43475).
Proof. exact (eq_refl (term1086 A _43472 _43475)). Qed.
Lemma lem3788921 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1097 A _43472 _43474 _43475 f _43473) = (term1107 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3788920 A _43472 _43475) (@lem3788919 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788932 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1096 A _43472 _43474 _43475 f _43473) = (term1107 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3788833 A _43472 _43474 _43475 f _43473) (@lem3788921 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788933 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1063 A f _43474 _43473 _43472 _43475) = (term1107 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3788828 A _43472 _43474 _43475 f _43473) (@lem3788932 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3788935 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1108 A f _43474 _43473 _43472 _43475) = (term1109 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3788934) (@lem3788933 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3788959 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788960 {A : Type'} (_43472 : A -> Prop) (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1110 A f _43472 _43474 _43473 _43475) = (term1111 A _43472 f _43474 _43473 _43475).
Proof. exact (@lem3788959 (term460 A _43472 _43474) (term477 A f _43473) (term1112 A _43474 _43473 _43475)). Qed.
Lemma lem3788974 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3788975 {A : Type'} (_43474 : A) (f : type686 A) (_43473 : A -> Prop) (_43475 : A) : (term1113 A f _43474 _43473 _43475) = (term1114 A _43474 f _43473 _43475).
Proof. exact (@lem3788974 (@I (A -> Prop) _43473 _43474) (term477 A f _43473) (term460 A _43473 _43475)). Qed.
Lemma lem3788989 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3788990 {A : Type'} (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1115 A f _43473 _43475) = (term1089 A _43475 f _43473).
Proof. exact (@lem3788989 (term460 A _43473 _43475) (term477 A f _43473)). Qed.
Lemma lem3788996 {A : Type'} (_43473 : A -> Prop) (_43474 : A) : (term1086 A _43473 _43474) = (term1086 A _43473 _43474).
Proof. exact (eq_refl (term1086 A _43473 _43474)). Qed.
Lemma lem3788997 {A : Type'} (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1114 A _43474 f _43473 _43475) = (term1092 A _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3788996 A _43473 _43474) (@lem3788990 A _43475 f _43473)). Qed.
Lemma lem3789008 {A : Type'} (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1113 A f _43474 _43473 _43475) = (term1092 A _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788975 A _43474 f _43473 _43475) (@lem3788997 A _43474 _43475 f _43473)). Qed.
Lemma lem3789009 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term490 A _43472 _43474) = (term490 A _43472 _43474).
Proof. exact (eq_refl (term490 A _43472 _43474)). Qed.
Lemma lem3789010 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1111 A _43472 f _43474 _43473 _43475) = (term1093 A _43472 _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3789009 A _43472 _43474) (@lem3789008 A _43474 _43475 f _43473)). Qed.
Lemma lem3789014 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3789015 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1093 A _43472 _43474 _43475 f _43473) = (term1094 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3789014 (@I (A -> Prop) _43473 _43474) (term460 A _43472 _43474) (term1089 A _43475 f _43473)). Qed.
Lemma lem3789041 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1111 A _43472 f _43474 _43473 _43475) = (term1094 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3789010 A _43472 _43474 _43475 f _43473) (@lem3789015 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3789042 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1110 A f _43472 _43474 _43473 _43475) = (term1094 A _43472 _43474 _43475 f _43473).
Proof. exact (TRANS (@lem3788960 A _43472 f _43474 _43473 _43475) (@lem3789041 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3789043 {A : Type'} (f : type686 A) (_43472 : A -> Prop) : (term478 A f _43472) = (term478 A f _43472).
Proof. exact (eq_refl (term478 A f _43472)). Qed.
Lemma lem3789044 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1116 A f _43472 _43474 _43473 _43475) = (term1098 A _43472 _43474 _43475 f _43473).
Proof. exact (MK_COMB (@lem3789043 A f _43472) (@lem3789042 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3789048 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3789049 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1098 A _43472 _43474 _43475 f _43473) = (term1099 A _43472 _43474 _43475 f _43473).
Proof. exact (@lem3789048 (@I (A -> Prop) _43473 _43474) (term477 A f _43472) (term1100 A _43472 _43474 _43475 f _43473)). Qed.
Lemma lem3789063 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3789064 {A : Type'} (_43474 : A) (_43472 : A -> Prop) (_43475 : A) (f : type686 A) (_43473 : A -> Prop) : (term1101 A _43472 _43474 _43475 f _43473) = (term1102 A _43474 _43472 _43475 f _43473).
Proof. exact (@lem3789063 (term460 A _43472 _43474) (term477 A f _43472) (term1089 A _43475 f _43473)). Qed.
Lemma lem3789078 (q : Prop) (p : Prop) (r : Prop) : (term555 p q r) = (term555 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3789079 {A : Type'} (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1103 A _43472 _43475 f _43473) = (term1104 A _43475 _43472 f _43473).
Proof. exact (@lem3789078 (term460 A _43473 _43475) (term477 A f _43472) (term477 A f _43473)). Qed.
Lemma lem3789095 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term490 A _43472 _43474) = (term490 A _43472 _43474).
Proof. exact (eq_refl (term490 A _43472 _43474)). Qed.
Lemma lem3789096 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1102 A _43474 _43472 _43475 f _43473) = (term1105 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3789095 A _43472 _43474) (@lem3789079 A _43475 _43472 f _43473)). Qed.
Lemma lem3789107 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1101 A _43472 _43474 _43475 f _43473) = (term1105 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3789064 A _43474 _43472 _43475 f _43473) (@lem3789096 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789108 {A : Type'} (_43473 : A -> Prop) (_43474 : A) : (term1086 A _43473 _43474) = (term1086 A _43473 _43474).
Proof. exact (eq_refl (term1086 A _43473 _43474)). Qed.
Lemma lem3789109 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1099 A _43472 _43474 _43475 f _43473) = (term1106 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3789108 A _43473 _43474) (@lem3789107 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789120 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1098 A _43472 _43474 _43475 f _43473) = (term1106 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3789049 A _43472 _43474 _43475 f _43473) (@lem3789109 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789121 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1116 A f _43472 _43474 _43473 _43475) = (term1106 A _43474 _43475 _43472 f _43473).
Proof. exact (TRANS (@lem3789044 A _43472 _43474 _43475 f _43473) (@lem3789120 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789122 {A : Type'} (_43472 : A -> Prop) (_43475 : A) : (term1086 A _43472 _43475) = (term1086 A _43472 _43475).
Proof. exact (eq_refl (term1086 A _43472 _43475)). Qed.
Lemma lem3789123 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : (term1117 A f _43472 _43474 _43473 _43475) = (term1107 A _43474 _43475 _43472 f _43473).
Proof. exact (MK_COMB (@lem3789122 A _43472 _43475) (@lem3789121 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789134 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : ((term1063 A f _43474 _43473 _43472 _43475) = (term1117 A f _43472 _43474 _43473 _43475)) = ((term1107 A _43474 _43475 _43472 f _43473) = (term1107 A _43474 _43475 _43472 f _43473)).
Proof. exact (MK_COMB (@lem3788935 A _43474 _43475 _43472 f _43473) (@lem3789123 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3789137 (x : Prop) : (x = x) = True.
Proof. exact (@lem3789136 Prop x). Qed.
Lemma lem3789138 {A : Type'} (_43474 : A) (_43475 : A) (_43472 : A -> Prop) (f : type686 A) (_43473 : A -> Prop) : ((term1107 A _43474 _43475 _43472 f _43473) = (term1107 A _43474 _43475 _43472 f _43473)) = True.
Proof. exact (@lem3789137 (term1107 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789139 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : ((term1063 A f _43474 _43473 _43472 _43475) = (term1117 A f _43472 _43474 _43473 _43475)) = True.
Proof. exact (TRANS (@lem3789134 A _43474 _43475 _43472 f _43473) (@lem3789138 A _43474 _43475 _43472 f _43473)). Qed.
Lemma lem3789140 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : True = ((term1063 A f _43474 _43473 _43472 _43475) = (term1117 A f _43472 _43474 _43473 _43475)).
Proof. exact (SYM (@lem3789139 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789141 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1063 A f _43474 _43473 _43472 _43475) = (term1117 A f _43472 _43474 _43473 _43475).
Proof. exact (EQ_MP (@lem3789140 A f _43472 _43474 _43473 _43475) (@lem0)). Qed.
Lemma lem3789142 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1117 A f _43472 _43474 _43473 _43475.
Proof. exact (EQ_MP (@lem3789141 A f _43472 _43474 _43473 _43475) (@lem3788451 A _43474 _43473 _43472 _43475 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3789144 (b : Prop) (a : Prop) : (a \/ b) = (term527 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3789145 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1117 A f _43472 _43474 _43473 _43475) = (term1118 A f _43474 _43473 _43472 _43475).
Proof. exact (@lem3789144 (term1116 A f _43472 _43474 _43473 _43475) (@I (A -> Prop) _43472 _43475)). Qed.
Lemma lem3789147 (a : Prop) (b : Prop) : (term1119 a b) = (term1120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3789148 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1121 A f _43472 _43474 _43473 _43475) = (term1122 A f _43472 _43474 _43473 _43475).
Proof. exact (@lem3789147 (term477 A f _43472) (term1110 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789150 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3789151 {A : Type'} (f : type686 A) (_43472 : A -> Prop) : (term529 A f _43472) = (@I ((A -> Prop) -> Prop) f _43472).
Proof. exact (@lem3789150 (@I ((A -> Prop) -> Prop) f _43472)). Qed.
Lemma lem3789152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3789153 {A : Type'} (f : type686 A) (_43472 : A -> Prop) : (term1123 A f _43472) = (term496 A f _43472).
Proof. exact (MK_COMB (@lem3789152) (@lem3789151 A f _43472)). Qed.
Lemma lem3789155 (a : Prop) (b : Prop) : (term1119 a b) = (term1120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3789156 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1124 A f _43472 _43474 _43473 _43475) = (term1125 A f _43472 _43474 _43473 _43475).
Proof. exact (@lem3789155 (term477 A f _43473) (term1126 A _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789158 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3789159 {A : Type'} (f : type686 A) (_43473 : A -> Prop) : (term529 A f _43473) = (@I ((A -> Prop) -> Prop) f _43473).
Proof. exact (@lem3789158 (@I ((A -> Prop) -> Prop) f _43473)). Qed.
Lemma lem3789160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3789161 {A : Type'} (f : type686 A) (_43473 : A -> Prop) : (term1123 A f _43473) = (term496 A f _43473).
Proof. exact (MK_COMB (@lem3789160) (@lem3789159 A f _43473)). Qed.
Lemma lem3789163 (a : Prop) (b : Prop) : (term1119 a b) = (term1120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3789164 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1127 A _43472 _43474 _43473 _43475) = (term1128 A _43472 _43474 _43473 _43475).
Proof. exact (@lem3789163 (term460 A _43472 _43474) (term1112 A _43474 _43473 _43475)). Qed.
Lemma lem3789166 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3789167 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term1129 A _43472 _43474) = (@I (A -> Prop) _43472 _43474).
Proof. exact (@lem3789166 (@I (A -> Prop) _43472 _43474)). Qed.
Lemma lem3789168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3789169 {A : Type'} (_43472 : A -> Prop) (_43474 : A) : (term1130 A _43472 _43474) = (term973 A _43472 _43474).
Proof. exact (MK_COMB (@lem3789168) (@lem3789167 A _43472 _43474)). Qed.
Lemma lem3789171 (a : Prop) (b : Prop) : (term1119 a b) = (term1120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3789172 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1131 A _43474 _43473 _43475) = (term1132 A _43474 _43473 _43475).
Proof. exact (@lem3789171 (@I (A -> Prop) _43473 _43474) (term460 A _43473 _43475)). Qed.
Lemma lem3789174 (a : Prop) : (term207 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3789175 {A : Type'} (_43473 : A -> Prop) (_43475 : A) : (term1129 A _43473 _43475) = (@I (A -> Prop) _43473 _43475).
Proof. exact (@lem3789174 (@I (A -> Prop) _43473 _43475)). Qed.
Lemma lem3789176 {A : Type'} (_43473 : A -> Prop) (_43474 : A) : (term1133 A _43473 _43474) = (term1133 A _43473 _43474).
Proof. exact (eq_refl (term1133 A _43473 _43474)). Qed.
Lemma lem3789177 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1132 A _43474 _43473 _43475) = (term1134 A _43474 _43473 _43475).
Proof. exact (MK_COMB (@lem3789176 A _43473 _43474) (@lem3789175 A _43473 _43475)). Qed.
Lemma lem3789178 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1131 A _43474 _43473 _43475) = (term1134 A _43474 _43473 _43475).
Proof. exact (TRANS (@lem3789172 A _43474 _43473 _43475) (@lem3789177 A _43474 _43473 _43475)). Qed.
Lemma lem3789179 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1128 A _43472 _43474 _43473 _43475) = (term1135 A _43472 _43474 _43473 _43475).
Proof. exact (MK_COMB (@lem3789169 A _43472 _43474) (@lem3789178 A _43474 _43473 _43475)). Qed.
Lemma lem3789180 {A : Type'} (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1127 A _43472 _43474 _43473 _43475) = (term1135 A _43472 _43474 _43473 _43475).
Proof. exact (TRANS (@lem3789164 A _43472 _43474 _43473 _43475) (@lem3789179 A _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789181 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1125 A f _43472 _43474 _43473 _43475) = (term1136 A f _43472 _43474 _43473 _43475).
Proof. exact (MK_COMB (@lem3789161 A f _43473) (@lem3789180 A _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789182 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1124 A f _43472 _43474 _43473 _43475) = (term1136 A f _43472 _43474 _43473 _43475).
Proof. exact (TRANS (@lem3789156 A f _43472 _43474 _43473 _43475) (@lem3789181 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789183 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1122 A f _43472 _43474 _43473 _43475) = (term1137 A f _43472 _43474 _43473 _43475).
Proof. exact (MK_COMB (@lem3789153 A f _43472) (@lem3789182 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789184 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1121 A f _43472 _43474 _43473 _43475) = (term1137 A f _43472 _43474 _43473 _43475).
Proof. exact (TRANS (@lem3789148 A f _43472 _43474 _43473 _43475) (@lem3789183 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3789186 {A : Type'} (f : type686 A) (_43472 : A -> Prop) (_43474 : A) (_43473 : A -> Prop) (_43475 : A) : (term1138 A f _43472 _43474 _43473 _43475) = (term1139 A f _43472 _43474 _43473 _43475).
Proof. exact (MK_COMB (@lem3789185) (@lem3789184 A f _43472 _43474 _43473 _43475)). Qed.
Lemma lem3789187 {A : Type'} (_43472 : A -> Prop) (_43475 : A) : (@I (A -> Prop) _43472 _43475) = (@I (A -> Prop) _43472 _43475).
Proof. exact (eq_refl (@I (A -> Prop) _43472 _43475)). Qed.
Lemma lem3789188 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1118 A f _43474 _43473 _43472 _43475) = (term1140 A f _43474 _43473 _43472 _43475).
Proof. exact (MK_COMB (@lem3789186 A f _43472 _43474 _43473 _43475) (@lem3789187 A _43472 _43475)). Qed.
Lemma lem3789189 {A : Type'} (f : type686 A) (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) : (term1117 A f _43472 _43474 _43473 _43475) = (term1140 A f _43474 _43473 _43472 _43475).
Proof. exact (TRANS (@lem3789145 A f _43474 _43473 _43472 _43475) (@lem3789188 A f _43474 _43473 _43472 _43475)). Qed.
Lemma lem3789191 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term1134 A x' s' x.
Proof. exact (conj (@lem3788632 A t x t' s' x' h1) (@lem3788639 A t x t' s' x' h1)). Qed.
Lemma lem3789192 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term1135 A t' x' s' x.
Proof. exact (conj (@lem3788625 A t x t' s' x' h1) (@lem3789191 A t x t' s' x' h1)). Qed.
Lemma lem3789193 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term1136 A f t' x' s' x.
Proof. exact (conj (@lem3788618 A t'' x'' x''' f t''' s t x t' s' x' h1 h2) (@lem3789192 A t x t' s' x' h2)). Qed.
Lemma lem3789194 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term1137 A f t' x' s' x.
Proof. exact (conj (@lem3788599 A t'' x'' x''' f t''' s t x t' s' x' h1 h2) (@lem3789193 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3789196 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1140 A f _43474 _43473 _43472 _43475.
Proof. exact (EQ_MP (@lem3789189 A f _43474 _43473 _43472 _43475) (@lem3789142 A _43472 _43474 _43473 _43475 t'' t x'' x''' f t''' s h1)). Qed.
Lemma lem3789197 {A : Type'} (_43474 : A) (_43473 : A -> Prop) (_43472 : A -> Prop) (_43475 : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1140 A f _43474 _43473 _43472 _43475.
Proof. exact (@lem3789196 A _43474 _43473 _43472 _43475 t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3789198 {A : Type'} (x' : A) (s' : A -> Prop) (t' : A -> Prop) (x : A) (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term765 A t'' t x'' x''' f t''' s) : term1140 A f x' s' t' x.
Proof. exact (@lem3789197 A x' s' t' x t'' t x'' x''' f t''' s h1). Qed.
Lemma lem3789201 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I (A -> Prop) t' x.
Proof. exact (@lem3789198 A x' s' t' x t'' t x'' x''' f t''' s h1 (@lem3789194 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3789202 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term1072 A t' x.
Proof. exact (fun h0 : term460 A t' x => @lem3789201 A t'' x'' x''' f t''' s t x t' s' x' h1 h2). Qed.
Lemma lem3789204 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3789205 {A : Type'} (t' : A -> Prop) (x : A) : (term1072 A t' x) = (@I (A -> Prop) t' x).
Proof. exact (@lem3789204 (@I (A -> Prop) t' x)). Qed.
Lemma lem3789206 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : @I (A -> Prop) t' x.
Proof. exact (EQ_MP (@lem3789205 A t' x) (@lem3789202 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3789209 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3789211 {A : Type'} (t' : A -> Prop) (x : A) : (term460 A t' x) = (term535 A t' x).
Proof. exact (@lem3789209 (@I (A -> Prop) t' x)). Qed.
Lemma lem3789214 {A : Type'} (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term979 A t x t' s' x') : term535 A t' x.
Proof. exact (EQ_MP (@lem3789211 A t' x) (@lem3788463 A t x t' s' x' h1)). Qed.
Lemma lem3789217 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : False.
Proof. exact (@lem3789214 A t x t' s' x' h2 (@lem3789206 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3789218 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : term537.
Proof. exact (fun h0 : ~ False => @lem3789217 A t'' x'' x''' f t''' s t x t' s' x' h1 h2). Qed.
Lemma lem3789220 (p : Prop) : (term523 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3789221 : term537 = False.
Proof. exact (@lem3789220 False). Qed.
Lemma lem3789222 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term979 A t x t' s' x') : False.
Proof. exact (EQ_MP (@lem3789221) (@lem3789218 A t'' x'' x''' f t''' s t x t' s' x' h1 h2)). Qed.
Lemma lem3789223 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : (term982 A t) = False.
Proof. exact (prop_ext (fun h3 : term982 A t => @lem3788514 A t'' t x'' x''' f t''' s h1 h2) (fun h3 : False => @lem3788325 A t h1)). Qed.
Lemma lem3789224 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3789223 A t'' t x'' x''' f t''' s h1 h2) (@lem3788325 A t h1)). Qed.
Lemma lem3789225 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : (term982 A t) = False.
Proof. exact (prop_ext (fun h3 : term982 A t => @lem3789224 A t'' t x'' x''' f t''' s h1 h2) (fun h3 : False => @lem3787732 A t h1)). Qed.
Lemma lem3789226 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3789225 A t'' t x'' x''' f t''' s h1 h2) (@lem3787732 A t h1)). Qed.
Lemma lem3789227 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term513 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : (term513 A t) = False.
Proof. exact (prop_ext (fun h3 : term513 A t => @lem3788539 A t'' t x'' x''' f t''' s h1 h2) (fun h3 : False => @lem3787960 A t h1)). Qed.
Lemma lem3789228 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term513 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3789227 A t'' t x'' x''' f t''' s h1 h2) (@lem3787960 A t h1)). Qed.
Lemma lem3789229 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : (term982 A t) = False.
Proof. exact (prop_ext (fun h3 : term982 A t => @lem3789226 A t'' t x'' x''' f t''' s h1 h2) (fun h3 : False => @lem3787732 A t h1)). Qed.
Lemma lem3789230 {A : Type'} (t'' : type1402 A) (t : type686 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (h1 : term982 A t) (h2 : term765 A t'' t x'' x''' f t''' s) : False.
Proof. exact (EQ_MP (@lem3789229 A t'' t x'' x''' f t''' s h1 h2) (@lem3787732 A t h1)). Qed.
Lemma lem3789231 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term981 A t x t' s' x') : False.
Proof. exact (or_elim (@lem3787495 A t x t' s' x' h2) (fun h0 : term513 A t => @lem3789228 A t'' t x'' x''' f t''' s h0 h1) (fun h0 : term979 A t x t' s' x' => @lem3789222 A t'' x'' x''' f t''' s t x t' s' x' h1 h0)). Qed.
Lemma lem3789232 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (t''' : type1402 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term765 A t'' t x'' x''' f t''' s) (h2 : term962 A t x t' s' x') : False.
Proof. exact (or_elim (@lem3787217 A t x t' s' x' h2) (fun h0 : term982 A t => @lem3789230 A t'' t x'' x''' f t''' s h0 h1) (fun h0 : term981 A t x t' s' x' => @lem3789231 A t'' x'' x''' f t''' s t x t' s' x' h1 h0)). Qed.
Lemma lem3789233 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (x''' : A -> Prop) (f : type686 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term768 A t'' t x'' x''' f s) (h2 : term962 A t x t' s' x') : False.
Proof. exact (ex_elim (@lem3787119 A t'' t x'' x''' f s h1) (fun t''' : type1402 A => fun h0 : term767 A t'' t x'' x''' f s t''' => @lem3789232 A t'' x'' x''' f t''' s t x t' s' x' h0 h2)). Qed.
Lemma lem3789234 {A : Type'} (t'' : type1402 A) (x'' : A -> Prop) (f : type686 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term770 A t'' t x'' f s) (h2 : term962 A t x t' s' x') : False.
Proof. exact (ex_elim (@lem3787118 A t'' t x'' f s h1) (fun x''' : A -> Prop => fun h0 : term769 A t'' t x'' f s x''' => @lem3789233 A t'' x'' x''' f s t x t' s' x' h0 h2)). Qed.
Lemma lem3789235 {A : Type'} (t'' : type1402 A) (f : type686 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term772 A t'' t f s) (h2 : term962 A t x t' s' x') : False.
Proof. exact (ex_elim (@lem3787117 A t'' t f s h1) (fun x'' : A -> Prop => fun h0 : term771 A t'' t f s x'' => @lem3789234 A t'' x'' f s t x t' s' x' h0 h2)). Qed.
Lemma lem3789236 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (x : A) (t' : A -> Prop) (s' : A -> Prop) (x' : A) (h1 : term582 A t f s) (h2 : term962 A t x t' s' x') : False.
Proof. exact (ex_elim (@lem3786619 A t f s h1) (fun t'' : type1402 A => fun h0 : term773 A t f s t'' => @lem3789235 A t'' f s t x t' s' x' h0 h2)). Qed.
Lemma lem3789237 {A : Type'} (x : A) (t' : A -> Prop) (s' : A -> Prop) (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term965 A t x t' s') (h2 : term582 A t f s) : False.
Proof. exact (ex_elim (@lem3787115 A t x t' s' h1) (fun x' : A => fun h0 : term964 A t x t' s' x' => @lem3789236 A f s t x t' s' x' h2 h0)). Qed.
Lemma lem3789238 {A : Type'} (t' : A -> Prop) (s' : A -> Prop) (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term967 A t t' s') (h2 : term582 A t f s) : False.
Proof. exact (ex_elim (@lem3787114 A t t' s' h1) (fun x : A => fun h0 : term966 A t t' s' x => @lem3789237 A x t' s' t f s h0 h2)). Qed.
Lemma lem3789239 {A : Type'} (s' : A -> Prop) (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term969 A t s') (h2 : term582 A t f s) : False.
Proof. exact (ex_elim (@lem3787113 A t s' h1) (fun t' : A -> Prop => fun h0 : term968 A t s' t' => @lem3789238 A t' s' t f s h0 h2)). Qed.
Lemma lem3789240 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term606 A t) (h2 : term582 A t f s) : False.
Proof. exact (ex_elim (@lem3787112 A t h1) (fun s' : A -> Prop => fun h0 : term970 A t s' => @lem3789239 A s' t f s h0 h2)). Qed.
Lemma lem3789241 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term606 A t) (h2 : term582 A t f s) : (term606 A t) = False.
Proof. exact (prop_ext (fun h3 : term606 A t => @lem3789240 A t f s h1 h2) (fun h3 : False => @lem3785661 A t h1)). Qed.
Lemma lem3789242 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term606 A t) (h2 : term582 A t f s) : False.
Proof. exact (EQ_MP (@lem3789241 A t f s h1 h2) (@lem3785661 A t h1)). Qed.
Lemma lem3789243 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term582 A t f s) : term605 A t.
Proof. exact (fun h0 : term606 A t => @lem3789242 A t f s h0 h1). Qed.
Lemma lem3789244 {A : Type'} (t : type686 A) (f : type686 A) (s : A -> Prop) (h1 : term582 A t f s) : term585 A t.
Proof. exact (EQ_MP (@lem3785660 A t) (@lem3789243 A t f s h1)). Qed.
Lemma lem3789245 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term586 A f s t.
Proof. exact (fun h0 : term582 A t f s => @lem3789244 A t f s h0). Qed.
Lemma lem3789250 {A : Type'} (s : A -> Prop) (t : type686 A) : term596 A s t.
Proof. exact (fun f : type686 A => @lem3789245 A f s t). Qed.
Lemma lem3789255 {A : Type'} (t : type686 A) : term600 A t.
Proof. exact (fun s : A -> Prop => @lem3789250 A s t). Qed.
Lemma lem3789260 {A : Type'} : term604 A.
Proof. exact (fun t : type686 A => @lem3789255 A t). Qed.
Lemma lem3789261 {A : Type'} : term603 A.
Proof. exact (EQ_MP (@lem3785655 A) (@lem3789260 A)). Qed.
Lemma lem3789262 {A : Type'} (t : type686 A) : term1141 A t.
Proof. exact (@lem3789261 A t). Qed.
Lemma lem3789263 {A : Type'} (t : type686 A) : (term1141 A t) = (term599 A t).
Proof. exact (eq_refl (term1141 A t)). Qed.
Lemma lem3789264 {A : Type'} (t : type686 A) : term599 A t.
Proof. exact (EQ_MP (@lem3789263 A t) (@lem3789262 A t)). Qed.
Lemma lem3789265 {A : Type'} (t : type686 A) (s : A -> Prop) : term1142 A t s.
Proof. exact (@lem3789264 A t s). Qed.
Lemma lem3789266 {A : Type'} (s : A -> Prop) (t : type686 A) : (term1142 A t s) = (term595 A s t).
Proof. exact (eq_refl (term1142 A t s)). Qed.
Lemma lem3789267 {A : Type'} (s : A -> Prop) (t : type686 A) : term595 A s t.
Proof. exact (EQ_MP (@lem3789266 A s t) (@lem3789265 A t s)). Qed.
Lemma lem3789268 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) : term1143 A s t f.
Proof. exact (@lem3789267 A s t f). Qed.
Lemma lem3789269 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : (term1143 A s t f) = (term587 A f s t).
Proof. exact (eq_refl (term1143 A s t f)). Qed.
Lemma lem3789270 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term587 A f s t.
Proof. exact (EQ_MP (@lem3789269 A f s t) (@lem3789268 A s t f)). Qed.
Lemma lem3789272 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term587 A f s t.
Proof. exact (@lem3785111 A f s t (@lem3789270 A f s t)). Qed.
Lemma lem3789273 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term588 A f s t) : False.
Proof. exact (@lem3789272 A f s t (@lem3785095 A f s t h1)). Qed.
Lemma lem3789274 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term588 A f s t) : (term588 A f s t) = False.
Proof. exact (prop_ext (fun h2 : term588 A f s t => @lem3789273 A f s t h1) (fun h2 : False => @lem3785095 A f s t h1)). Qed.
Lemma lem3789275 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term588 A f s t) : False.
Proof. exact (EQ_MP (@lem3789274 A f s t h1) (@lem3785095 A f s t h1)). Qed.
Lemma lem3789276 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term587 A f s t.
Proof. exact (fun h0 : term588 A f s t => @lem3789275 A f s t h0). Qed.
Lemma lem3789277 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term586 A f s t.
Proof. exact (EQ_MP (@lem3785094 A f s t) (@lem3789276 A f s t)). Qed.
Lemma lem3789278 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term571 A f s t.
Proof. exact (EQ_MP (@lem3785090 A f s t) (@lem3789277 A f s t)). Qed.
Lemma lem3789279 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) : term570 A f s t.
Proof. exact (EQ_MP (@lem3784595 A f s t) (@lem3789278 A f s t)). Qed.
Lemma lem3789280 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term3 A t.
Proof. exact (@lem3789279 A f s t (@lem3784334 A s t f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3789281 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term4 A t.
Proof. exact (@lem3784317 A t (@lem3789280 A s t f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3789282 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term544 A t f.
Proof. exact (@lem3784313 A t f h8 (@lem3789281 A s t f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3789283 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term542 A f s t.
Proof. exact (EQ_MP (@lem3784253 A f s t h7) (@lem3789282 A s t f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3789284 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term36 A f s.
Proof. exact (ex_intro (term126 A f s) (@UNIONS A t) (@lem3789283 A s t f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3789285 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term45 A f s t) : term70 A f s t.
Proof. exact (proj2 (@lem3784194 A f s t h1)). Qed.
Lemma lem3789286 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term45 A f s t) : @FINITE (A -> Prop) t.
Proof. exact (proj1 (@lem3784194 A f s t h1)). Qed.
Lemma lem3789287 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term70 A f s t) : term22 A s t.
Proof. exact (proj2 (@lem3784195 A f s t h1)). Qed.
Lemma lem3789288 {A : Type'} (f : type686 A) (s : A -> Prop) (t : type686 A) (h1 : term70 A f s t) : @SUBSET (A -> Prop) t f.
Proof. exact (proj1 (@lem3784195 A f s t h1)). Qed.
Lemma lem3789289 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : (term22 A s t) = (term36 A f s).
Proof. exact (prop_ext (fun h9 : term22 A s t => @lem3789284 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term36 A f s => @lem3784197 A s t h7)). Qed.
Lemma lem3789290 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789289 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (@lem3784197 A s t h7)). Qed.
Lemma lem3789291 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : (@SUBSET (A -> Prop) t f) = (term36 A f s).
Proof. exact (prop_ext (fun h9 : @SUBSET (A -> Prop) t f => @lem3789290 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term36 A f s => @lem3784198 A t f h8)). Qed.
Lemma lem3789292 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term22 A s f) (h7 : term22 A s t) (h8 : @SUBSET (A -> Prop) t f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789291 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (@lem3784198 A t f h8)). Qed.
Lemma lem3789293 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) (h8 : @SUBSET (A -> Prop) t f) : (term22 A s t) = (term36 A f s).
Proof. exact (prop_ext (fun h9 : term22 A s t => @lem3789292 A s t f h1 h2 h3 h4 h5 h7 h9 h8) (fun h9 : term36 A f s => @lem3789287 A f s t h6)). Qed.
Lemma lem3789294 {A : Type'} (s : A -> Prop) (t : type686 A) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) (h8 : @SUBSET (A -> Prop) t f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789293 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (@lem3789287 A f s t h6)). Qed.
Lemma lem3789295 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) : (@SUBSET (A -> Prop) t f) = (term36 A f s).
Proof. exact (prop_ext (fun h8 : @SUBSET (A -> Prop) t f => @lem3789294 A s t f h1 h2 h3 h4 h5 h6 h7 h8) (fun h8 : term36 A f s => @lem3789288 A f s t h6)). Qed.
Lemma lem3789296 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789295 A t s f h1 h2 h3 h4 h5 h6 h7) (@lem3789288 A f s t h6)). Qed.
Lemma lem3789297 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) : (@FINITE (A -> Prop) t) = (term36 A f s).
Proof. exact (prop_ext (fun h8 : @FINITE (A -> Prop) t => @lem3789296 A t s f h1 h2 h3 h4 h5 h6 h7) (fun h8 : term36 A f s => @lem3784196 A t h3)). Qed.
Lemma lem3789298 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term70 A f s t) (h7 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789297 A t s f h1 h2 h3 h4 h5 h6 h7) (@lem3784196 A t h3)). Qed.
Lemma lem3789299 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term45 A f s t) (h7 : term22 A s f) : (term70 A f s t) = (term36 A f s).
Proof. exact (prop_ext (fun h8 : term70 A f s t => @lem3789298 A t s f h1 h2 h3 h4 h5 h8 h7) (fun h8 : term36 A f s => @lem3789285 A f s t h6)). Qed.
Lemma lem3789300 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : @FINITE (A -> Prop) t) (h4 : term13 A f) (h5 : term13 A t) (h6 : term45 A f s t) (h7 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789299 A t s f h1 h2 h3 h4 h5 h6 h7) (@lem3789285 A f s t h6)). Qed.
Lemma lem3789301 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term13 A t) (h5 : term45 A f s t) (h6 : term22 A s f) : (@FINITE (A -> Prop) t) = (term36 A f s).
Proof. exact (prop_ext (fun h7 : @FINITE (A -> Prop) t => @lem3789300 A t s f h1 h2 h7 h3 h4 h5 h6) (fun h7 : term36 A f s => @lem3789286 A f s t h5)). Qed.
Lemma lem3789302 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term13 A t) (h5 : term45 A f s t) (h6 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789301 A t s f h1 h2 h3 h4 h5 h6) (@lem3789286 A f s t h5)). Qed.
Lemma lem3789303 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term13 A t) (h5 : term22 A s f) : term54 A t f s.
Proof. exact (fun h0 : term45 A f s t => @lem3789302 A t s f h1 h2 h3 h4 h0 h5). Qed.
Lemma lem3789304 {A : Type'} (t : type686 A) (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term54 A t f s.
Proof. exact (or_elim (@lem3781481 A t) (fun h0 : t = (@EMPTY (A -> Prop)) => @lem3784193 A t s f h1 h2 h3 h0 h4) (fun h0 : term13 A t => @lem3789303 A t s f h1 h2 h3 h0 h4)). Qed.
Lemma lem3789309 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term57 A f s.
Proof. exact (fun t : type686 A => @lem3789304 A t s f h1 h2 h3 h4). Qed.
Lemma lem3789310 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term37 A f s.
Proof. exact (EQ_MP (@lem3781621 A s f h2 h4) (@lem3789309 A s f h1 h2 h3 h4)). Qed.
Lemma lem3789311 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term36 A f s.
Proof. exact (@lem3789310 A s f h1 h2 h3 h4 (@lem3781490 A f s)). Qed.
Lemma lem3789312 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term19 A s f) : term20 A s f.
Proof. exact (proj2 (@lem3781491 A s f h1)). Qed.
Lemma lem3789313 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term19 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem3781491 A s f h1)). Qed.
Lemma lem3789314 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term20 A s f) : term21 A f.
Proof. exact (proj2 (@lem3781492 A s f h1)). Qed.
Lemma lem3789315 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term20 A s f) : term22 A s f.
Proof. exact (proj1 (@lem3781492 A s f h1)). Qed.
Lemma lem3789316 {A : Type'} (f : type686 A) (h1 : term21 A f) : term23 A f.
Proof. exact (proj2 (@lem3781494 A f h1)). Qed.
Lemma lem3789317 {A : Type'} (f : type686 A) (h1 : term21 A f) : term13 A f.
Proof. exact (proj1 (@lem3781494 A f h1)). Qed.
Lemma lem3789318 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : (term23 A f) = (term36 A f s).
Proof. exact (prop_ext (fun h5 : term23 A f => @lem3789311 A s f h1 h2 h3 h4) (fun h5 : term36 A f s => @lem3781496 A f h1)). Qed.
Lemma lem3789319 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789318 A s f h1 h2 h3 h4) (@lem3781496 A f h1)). Qed.
Lemma lem3789320 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : (term13 A f) = (term36 A f s).
Proof. exact (prop_ext (fun h5 : term13 A f => @lem3789319 A s f h1 h2 h3 h4) (fun h5 : term36 A f s => @lem3781497 A f h3)). Qed.
Lemma lem3789321 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A f) (h2 : @FINITE A s) (h3 : term13 A f) (h4 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789320 A s f h1 h2 h3 h4) (@lem3781497 A f h3)). Qed.
Lemma lem3789322 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term13 A f) (h3 : term21 A f) (h4 : term22 A s f) : (term23 A f) = (term36 A f s).
Proof. exact (prop_ext (fun h5 : term23 A f => @lem3789321 A s f h5 h1 h2 h4) (fun h5 : term36 A f s => @lem3789316 A f h3)). Qed.
Lemma lem3789323 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term13 A f) (h3 : term21 A f) (h4 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789322 A s f h1 h2 h3 h4) (@lem3789316 A f h3)). Qed.
Lemma lem3789324 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term21 A f) (h3 : term22 A s f) : (term13 A f) = (term36 A f s).
Proof. exact (prop_ext (fun h4 : term13 A f => @lem3789323 A s f h1 h4 h2 h3) (fun h4 : term36 A f s => @lem3789317 A f h2)). Qed.
Lemma lem3789325 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term21 A f) (h3 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789324 A s f h1 h2 h3) (@lem3789317 A f h2)). Qed.
Lemma lem3789326 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term21 A f) (h3 : term22 A s f) : (term22 A s f) = (term36 A f s).
Proof. exact (prop_ext (fun h4 : term22 A s f => @lem3789325 A s f h1 h2 h3) (fun h4 : term36 A f s => @lem3781495 A s f h3)). Qed.
Lemma lem3789327 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term21 A f) (h3 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789326 A s f h1 h2 h3) (@lem3781495 A s f h3)). Qed.
Lemma lem3789328 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) (h3 : term22 A s f) : (term21 A f) = (term36 A f s).
Proof. exact (prop_ext (fun h4 : term21 A f => @lem3789327 A s f h1 h4 h3) (fun h4 : term36 A f s => @lem3789314 A s f h2)). Qed.
Lemma lem3789329 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) (h3 : term22 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789328 A s f h1 h2 h3) (@lem3789314 A s f h2)). Qed.
Lemma lem3789330 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) : (term22 A s f) = (term36 A f s).
Proof. exact (prop_ext (fun h3 : term22 A s f => @lem3789329 A s f h1 h2 h3) (fun h3 : term36 A f s => @lem3789315 A s f h2)). Qed.
Lemma lem3789331 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789330 A s f h1 h2) (@lem3789315 A s f h2)). Qed.
Lemma lem3789332 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) : (@FINITE A s) = (term36 A f s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem3789331 A s f h1 h2) (fun h3 : term36 A f s => @lem3781493 A s h1)). Qed.
Lemma lem3789333 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term20 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789332 A s f h1 h2) (@lem3781493 A s h1)). Qed.
Lemma lem3789334 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term19 A s f) : (term20 A s f) = (term36 A f s).
Proof. exact (prop_ext (fun h3 : term20 A s f => @lem3789333 A s f h1 h3) (fun h3 : term36 A f s => @lem3789312 A s f h2)). Qed.
Lemma lem3789335 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term19 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789334 A s f h1 h2) (@lem3789312 A s f h2)). Qed.
Lemma lem3789336 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term19 A s f) : (@FINITE A s) = (term36 A f s).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem3789335 A s f h2 h1) (fun h2 : term36 A f s => @lem3789313 A s f h1)). Qed.
Lemma lem3789337 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term19 A s f) : term36 A f s.
Proof. exact (EQ_MP (@lem3789336 A s f h1) (@lem3789313 A s f h1)). Qed.
Lemma lem3789338 {A : Type'} (f : type686 A) (s : A -> Prop) : term1144 A f s.
Proof. exact (fun h0 : term19 A s f => @lem3789337 A s f h0). Qed.
Lemma lem3789343 {A : Type'} (f : type686 A) : term1145 A f.
Proof. exact (fun s : A -> Prop => @lem3789338 A f s). Qed.
Lemma lem3789348 {A : Type'} : term1146 A.
Proof. exact (fun f : type686 A => @lem3789343 A f). Qed.
