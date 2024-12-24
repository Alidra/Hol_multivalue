Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BOUND_GEN_term_abbrevs.
Require Import CARD_EQ_0_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_RDIV_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NSUM_BOUND_spec.
Require Import NSUM_LMUL_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem6970589 (a : nat) : term0 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem6970590 (a : nat) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem6970591 (a : nat) : term1 a.
Proof. exact (EQ_MP (@lem6970590 a) (@lem6970589 a)). Qed.
Lemma lem6970592 (a : nat) (b : nat) : term2 a b.
Proof. exact (@lem6970591 a b). Qed.
Lemma lem6970593 (a : nat) (b : nat) : (term2 a b) = (term3 a b).
Proof. exact (eq_refl (term2 a b)). Qed.
Lemma lem6970594 (a : nat) (b : nat) : term3 a b.
Proof. exact (EQ_MP (@lem6970593 a b) (@lem6970592 a b)). Qed.
Lemma lem6970595 (a : nat) (b : nat) (n : nat) : term4 a b n.
Proof. exact (@lem6970594 a b n). Qed.
Lemma lem6970596 (a : nat) (n : nat) (b : nat) : (term4 a b n) = (term5 a n b).
Proof. exact (eq_refl (term4 a b n)). Qed.
Lemma lem6970597 (a : nat) (n : nat) (b : nat) : term5 a n b.
Proof. exact (EQ_MP (@lem6970596 a n b) (@lem6970595 a b n)). Qed.
Lemma lem6970598 (a : nat) (h1 : term6 a) : term6 a.
Proof. exact (h1). Qed.
Lemma lem6970599 (n : nat) (b : nat) (a : nat) (h1 : term6 a) : (term7 n b a) = (term8 a n b).
Proof. exact (@lem6970597 a n b (@lem6970598 a h1)). Qed.
Lemma lem6970605 {_99911 : Type'} (s : _99911 -> Prop) : term9 _99911 s.
Proof. exact (@lem3854502 _99911 s). Qed.
Lemma lem6970606 {_99911 : Type'} (s : _99911 -> Prop) : (term9 _99911 s) = (term10 _99911 s).
Proof. exact (eq_refl (term9 _99911 s)). Qed.
Lemma lem6970607 {_99911 : Type'} (s : _99911 -> Prop) : term10 _99911 s.
Proof. exact (EQ_MP (@lem6970606 _99911 s) (@lem6970605 _99911 s)). Qed.
Lemma lem6970608 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : @FINITE _99911 s.
Proof. exact (h1). Qed.
Lemma lem6970609 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : ((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911)).
Proof. exact (@lem6970607 _99911 s (@lem6970608 _99911 s h1)). Qed.
Lemma lem6970628 (p : Prop) (q : Prop) (r : Prop) : (term11 p q r) = (term12 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6970629 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term13 A s f b) = (term14 A s f b).
Proof. exact (@lem6970628 (@FINITE A s) (term15 A f b s) (term16 A s f b)). Qed.
Lemma lem6970633 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970634 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6970633 p q p' q'). Qed.
Lemma lem6970635 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6970634 p q p'). Qed.
Lemma lem6970636 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term20 A s f b.
Proof. exact (@lem6970635 (@FINITE A s) (term21 A s f b)). Qed.
Lemma lem6970637 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term22 A s f b p'.
Proof. exact (@lem6970636 A s f b p'). Qed.
Lemma lem6970638 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term22 A s f b p') = (term23 A s f b p').
Proof. exact (eq_refl (term22 A s f b p')). Qed.
Lemma lem6970639 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term23 A s f b p'.
Proof. exact (EQ_MP (@lem6970638 A s f b p') (@lem6970637 A s f b p')). Qed.
Lemma lem6970640 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term24 A s f b p' q'.
Proof. exact (@lem6970639 A s f b p' q'). Qed.
Lemma lem6970641 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term24 A s f b p' q') = (term25 A s f b p' q').
Proof. exact (eq_refl (term24 A s f b p' q')). Qed.
Lemma lem6970642 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term25 A s f b p' q'.
Proof. exact (EQ_MP (@lem6970641 A s f b p' q') (@lem6970640 A s f b p' q')). Qed.
Lemma lem6970643 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem6970644 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (q' : Prop) : term26 A f b s q'.
Proof. exact (@lem6970642 A s f b (@FINITE A s) q'). Qed.
Lemma lem6970645 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (q' : Prop) : term27 A f b s q'.
Proof. exact (@lem6970644 A f b s q' (@lem6970643 A s)). Qed.
Lemma lem6970646 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6970647 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6970650 (p : Prop) (q : Prop) (r : Prop) : (term11 p q r) = (term12 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6970651 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term21 A s f b) = (term28 A s f b).
Proof. exact (@lem6970650 (term29 A s) (term30 A f b s) (term16 A s f b)). Qed.
Lemma lem6970655 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970656 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6970655 p q p' q'). Qed.
Lemma lem6970657 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6970656 p q p'). Qed.
Lemma lem6970658 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term31 A s f b.
Proof. exact (@lem6970657 (term29 A s) (term32 A s f b)). Qed.
Lemma lem6970659 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term33 A s f b p'.
Proof. exact (@lem6970658 A s f b p'). Qed.
Lemma lem6970660 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term33 A s f b p') = (term34 A s f b p').
Proof. exact (eq_refl (term33 A s f b p')). Qed.
Lemma lem6970661 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term34 A s f b p'.
Proof. exact (EQ_MP (@lem6970660 A s f b p') (@lem6970659 A s f b p')). Qed.
Lemma lem6970662 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term35 A s f b p' q'.
Proof. exact (@lem6970661 A s f b p' q'). Qed.
Lemma lem6970663 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term35 A s f b p' q') = (term36 A s f b p' q').
Proof. exact (eq_refl (term35 A s f b p' q')). Qed.
Lemma lem6970664 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term36 A s f b p' q'.
Proof. exact (EQ_MP (@lem6970663 A s f b p' q') (@lem6970662 A s f b p' q')). Qed.
Lemma lem6970667 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem6970668 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (q' : Prop) : term37 A f b s q'.
Proof. exact (@lem6970664 A s f b (term29 A s) q'). Qed.
Lemma lem6970669 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (q' : Prop) : term38 A f b s q'.
Proof. exact (@lem6970668 A f b s q' (@lem6970667 A s)). Qed.
Lemma lem6970670 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : term29 A s.
Proof. exact (h1). Qed.
Lemma lem6970671 {A : Type'} (s : A -> Prop) : term39 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem6970687 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970688 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6970687 p q p' q'). Qed.
Lemma lem6970689 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6970688 p q p'). Qed.
Lemma lem6970690 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term40 A s f b.
Proof. exact (@lem6970689 (term30 A f b s) (term16 A s f b)). Qed.
Lemma lem6970691 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term41 A s f b p'.
Proof. exact (@lem6970690 A s f b p'). Qed.
Lemma lem6970692 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term41 A s f b p') = (term42 A s f b p').
Proof. exact (eq_refl (term41 A s f b p')). Qed.
Lemma lem6970693 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term42 A s f b p'.
Proof. exact (EQ_MP (@lem6970692 A s f b p') (@lem6970691 A s f b p')). Qed.
Lemma lem6970694 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term43 A s f b p' q'.
Proof. exact (@lem6970693 A s f b p' q'). Qed.
Lemma lem6970695 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term43 A s f b p' q') = (term44 A s f b p' q').
Proof. exact (eq_refl (term43 A s f b p' q')). Qed.
Lemma lem6970696 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term44 A s f b p' q'.
Proof. exact (EQ_MP (@lem6970695 A s f b p' q') (@lem6970694 A s f b p' q')). Qed.
Lemma lem6970704 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970705 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6970704 p q p' q'). Qed.
Lemma lem6970706 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6970705 p q p'). Qed.
Lemma lem6970707 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) : term45 A f x b s.
Proof. exact (@lem6970706 (@IN A x s) (term46 A f x b s)). Qed.
Lemma lem6970708 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) : term47 A f x b s p'.
Proof. exact (@lem6970707 A f x b s p'). Qed.
Lemma lem6970709 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) : (term47 A f x b s p') = (term48 A f x b s p').
Proof. exact (eq_refl (term47 A f x b s p')). Qed.
Lemma lem6970710 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) : term48 A f x b s p'.
Proof. exact (EQ_MP (@lem6970709 A f x b s p') (@lem6970708 A f x b s p')). Qed.
Lemma lem6970711 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term49 A f x b s p' q'.
Proof. exact (@lem6970710 A f x b s p' q'). Qed.
Lemma lem6970712 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term49 A f x b s p' q') = (term50 A f x b s p' q').
Proof. exact (eq_refl (term49 A f x b s p' q')). Qed.
Lemma lem6970713 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (p' : Prop) (q' : Prop) : term50 A f x b s p' q'.
Proof. exact (EQ_MP (@lem6970712 A f x b s p' q') (@lem6970711 A f x b s p' q')). Qed.
Lemma lem6970714 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6970715 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term51 A f b x s q'.
Proof. exact (@lem6970713 A f x b s (@IN A x s) q'). Qed.
Lemma lem6970716 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term52 A f b x s q'.
Proof. exact (@lem6970715 A f b x s q' (@lem6970714 A x s)). Qed.
Lemma lem6970721 (a : nat) (n : nat) (b : nat) : term5 a n b.
Proof. exact (fun h0 : term6 a => @lem6970599 n b a h0). Qed.
Lemma lem6970722 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : term53 A s f x b.
Proof. exact (@lem6970721 (@CARD A s) (f x) b). Qed.
Lemma lem6970724 {_99911 : Type'} (s : _99911 -> Prop) : term10 _99911 s.
Proof. exact (fun h0 : @FINITE _99911 s => @lem6970609 _99911 s h0). Qed.
Lemma lem6970725 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem6970724 A s). Qed.
Lemma lem6970727 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6970647 A s) (@lem6970646 A s h1)). Qed.
Lemma lem6970728 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6970727 A s h1)). Qed.
Lemma lem6970729 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6970728 A s h1) (@lem0)). Qed.
Lemma lem6970730 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : ((@CARD A s) = (NUMERAL 0)) = (s = (@EMPTY A)).
Proof. exact (@lem6970725 A s (@lem6970729 A s h1)). Qed.
Lemma lem6970732 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem6970671 A s (@lem6970670 A s h1)). Qed.
Lemma lem6970733 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : ((@CARD A s) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem6970730 A s h1) (@lem6970732 A s h2)). Qed.
Lemma lem6970734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6970735 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term54 A s) = (~ False).
Proof. exact (MK_COMB (@lem6970734) (@lem6970733 A s h1 h2)). Qed.
Lemma lem6970737 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6970738 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term54 A s) = True.
Proof. exact (TRANS (@lem6970735 A s h1 h2) (@lem6970737)). Qed.
Lemma lem6970739 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : True = (term54 A s).
Proof. exact (SYM (@lem6970738 A s h1 h2)). Qed.
Lemma lem6970740 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term54 A s.
Proof. exact (EQ_MP (@lem6970739 A s h1 h2) (@lem0)). Qed.
Lemma lem6970741 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term46 A f x b s) = (term55 A s f x b).
Proof. exact (@lem6970722 A s f x b (@lem6970740 A s h1 h2)). Qed.
Lemma lem6970742 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term56 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem6970741 A f x b s h1 h2). Qed.
Lemma lem6970743 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : term57 A s f x b.
Proof. exact (@lem6970716 A f b x s (term55 A s f x b)). Qed.
Lemma lem6970744 {A : Type'} (f : A -> nat) (x : A) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term58 A f x b s) = (term59 A s f x b).
Proof. exact (@lem6970743 A s f x b (@lem6970742 A f x b s h1 h2)). Qed.
Lemma lem6970768 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term60 A f b s) = (term61 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6970744 A f x b s h1 h2)). Qed.
Lemma lem6970792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6970793 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term30 A f b s) = (term62 A s f b).
Proof. exact (MK_COMB (@lem6970792 A) (@lem6970768 A f b s h1 h2)). Qed.
Lemma lem6970821 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (q' : Prop) : term63 A s f b q'.
Proof. exact (@lem6970696 A s f b (term62 A s f b) q'). Qed.
Lemma lem6970822 {A : Type'} (f : A -> nat) (b : nat) (q' : Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term64 A s f b q'.
Proof. exact (@lem6970821 A s f b q' (@lem6970793 A f b s h1 h2)). Qed.
Lemma lem6970836 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term16 A s f b) = (term16 A s f b).
Proof. exact (eq_refl (term16 A s f b)). Qed.
Lemma lem6970837 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term65 A s f b.
Proof. exact (fun h0 : term62 A s f b => @lem6970836 A s f b). Qed.
Lemma lem6970838 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term66 A s f b.
Proof. exact (@lem6970822 A f b (term16 A s f b) s h1 h2). Qed.
Lemma lem6970839 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term32 A s f b) = (term67 A s f b).
Proof. exact (@lem6970838 A f b s h1 h2 (@lem6970837 A s f b)). Qed.
Lemma lem6970927 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : term68 A s f b.
Proof. exact (fun h0 : term29 A s => @lem6970839 A f b s h1 h0). Qed.
Lemma lem6970928 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term69 A s f b.
Proof. exact (@lem6970669 A f b s (term67 A s f b)). Qed.
Lemma lem6970929 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term28 A s f b) = (term70 A s f b).
Proof. exact (@lem6970928 A s f b (@lem6970927 A f b s h1)). Qed.
Lemma lem6971142 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term21 A s f b) = (term70 A s f b).
Proof. exact (TRANS (@lem6970651 A s f b) (@lem6970929 A f b s h1)). Qed.
Lemma lem6971143 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term71 A s f b.
Proof. exact (fun h0 : @FINITE A s => @lem6971142 A f b s h0). Qed.
Lemma lem6971144 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term72 A s f b.
Proof. exact (@lem6970645 A f b s (term70 A s f b)). Qed.
Lemma lem6971145 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term14 A s f b) = (term73 A s f b).
Proof. exact (@lem6971144 A s f b (@lem6971143 A s f b)). Qed.
Lemma lem6971593 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term13 A s f b) = (term73 A s f b).
Proof. exact (TRANS (@lem6970629 A s f b) (@lem6971145 A s f b)). Qed.
Lemma lem6971594 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term74 A s f) = (term75 A s f).
Proof. exact (fun_ext (fun b : nat => @lem6971593 A s f b)). Qed.
Lemma lem6972042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6972043 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term76 A s f) = (term77 A s f).
Proof. exact (MK_COMB (@lem6972042) (@lem6971594 A s f)). Qed.
Lemma lem6972495 {A : Type'} (s : A -> Prop) : (term78 A s) = (term79 A s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6972043 A s f)). Qed.
Lemma lem6972947 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6972948 {A : Type'} (s : A -> Prop) : (term80 A s) = (term81 A s).
Proof. exact (MK_COMB (@lem6972947 A) (@lem6972495 A s)). Qed.
Lemma lem6973404 {A : Type'} : (term82 A) = (term83 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6972948 A s)). Qed.
Lemma lem6973860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6973861 {A : Type'} : (term84 A) = (term85 A).
Proof. exact (MK_COMB (@lem6973860 A) (@lem6973404 A)). Qed.
Lemma lem6974321 {A : Type'} : (term85 A) = (term84 A).
Proof. exact (SYM (@lem6973861 A)). Qed.
Lemma lem6974322 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6974323 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : term29 A s.
Proof. exact (h1). Qed.
Lemma lem6974324 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term62 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974325 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (h1 : term86 A f s b) : term86 A f s b.
Proof. exact (h1). Qed.
Lemma lem6974326 {A : Type'} (s : A -> Prop) : term87 A s.
Proof. exact (@lem6970588 A s). Qed.
Lemma lem6974327 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem6974328 {A : Type'} (s : A -> Prop) : term88 A s.
Proof. exact (EQ_MP (@lem6974327 A s) (@lem6974326 A s)). Qed.
Lemma lem6974329 {A : Type'} (s : A -> Prop) (f : A -> nat) : term89 A s f.
Proof. exact (@lem6974328 A s f). Qed.
Lemma lem6974330 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term89 A s f) = (term90 A f s).
Proof. exact (eq_refl (term89 A s f)). Qed.
Lemma lem6974331 {A : Type'} (f : A -> nat) (s : A -> Prop) : term90 A f s.
Proof. exact (EQ_MP (@lem6974330 A f s) (@lem6974329 A s f)). Qed.
Lemma lem6974332 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term91 A f s b.
Proof. exact (@lem6974331 A f s b). Qed.
Lemma lem6974333 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term91 A f s b) = (term92 A f s b).
Proof. exact (eq_refl (term91 A f s b)). Qed.
Lemma lem6974334 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term92 A f s b.
Proof. exact (EQ_MP (@lem6974333 A f s b) (@lem6974332 A f s b)). Qed.
Lemma lem6974335 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term93 A s f b) : term93 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974336 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term93 A s f b) : term94 A f s b.
Proof. exact (@lem6974334 A f s b (@lem6974335 A s f b h1)). Qed.
Lemma lem6974337 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term94 A f s b) = ((term94 A f s b) = True).
Proof. exact (@lem7 (term94 A f s b)). Qed.
Lemma lem6974338 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term93 A s f b) : (term94 A f s b) = True.
Proof. exact (EQ_MP (@lem6974337 A f s b) (@lem6974336 A s f b h1)). Qed.
Lemma lem6974344 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6974359 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term95 A s f b x.
Proof. exact (@lem6974324 A s f b h1 x). Qed.
Lemma lem6974360 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term95 A s f b x) = (term59 A s f x b).
Proof. exact (eq_refl (term95 A s f b x)). Qed.
Lemma lem6974361 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term59 A s f x b.
Proof. exact (EQ_MP (@lem6974360 A s f x b) (@lem6974359 A x s f b h1)). Qed.
Lemma lem6974362 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6974363 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @IN A x s) : term55 A s f x b.
Proof. exact (@lem6974361 A x s f b h1 (@lem6974362 A x s h2)). Qed.
Lemma lem6974364 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term55 A s f x b) = ((term55 A s f x b) = True).
Proof. exact (@lem7 (term55 A s f x b)). Qed.
Lemma lem6974365 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @IN A x s) : (term55 A s f x b) = True.
Proof. exact (EQ_MP (@lem6974364 A s f x b) (@lem6974363 A f b x s h1 h2)). Qed.
Lemma lem6974372 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term96 A f s b.
Proof. exact (fun h0 : term93 A s f b => @lem6974338 A s f b h0). Qed.
Lemma lem6974373 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term96 A f s b.
Proof. exact (@lem6974372 A f s b). Qed.
Lemma lem6974374 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term97 A f s b.
Proof. exact (@lem6974373 A (term98 A s f) s b). Qed.
Lemma lem6974378 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6974344 A s) (@lem6974322 A s h1)). Qed.
Lemma lem6974379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6974380 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s) = (and True).
Proof. exact (MK_COMB (@lem6974379) (@lem6974378 A s h1)). Qed.
Lemma lem6974388 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6974389 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6974388 p q p' q'). Qed.
Lemma lem6974390 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6974389 p q p'). Qed.
Lemma lem6974391 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : term100 A s f x b.
Proof. exact (@lem6974390 (@IN A x s) (term101 A s f x b)). Qed.
Lemma lem6974392 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) : term102 A s f x b p'.
Proof. exact (@lem6974391 A s f x b p'). Qed.
Lemma lem6974393 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) : (term102 A s f x b p') = (term103 A s f x b p').
Proof. exact (eq_refl (term102 A s f x b p')). Qed.
Lemma lem6974394 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) : term103 A s f x b p'.
Proof. exact (EQ_MP (@lem6974393 A s f x b p') (@lem6974392 A s f x b p')). Qed.
Lemma lem6974395 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : term104 A s f x b p' q'.
Proof. exact (@lem6974394 A s f x b p' q'). Qed.
Lemma lem6974396 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : (term104 A s f x b p' q') = (term105 A s f x b p' q').
Proof. exact (eq_refl (term104 A s f x b p' q')). Qed.
Lemma lem6974397 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (p' : Prop) (q' : Prop) : term105 A s f x b p' q'.
Proof. exact (EQ_MP (@lem6974396 A s f x b p' q') (@lem6974395 A s f x b p' q')). Qed.
Lemma lem6974398 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6974399 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term106 A f b x s q'.
Proof. exact (@lem6974397 A s f x b (@IN A x s) q'). Qed.
Lemma lem6974400 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term107 A f b x s q'.
Proof. exact (@lem6974399 A f b x s q' (@lem6974398 A x s)). Qed.
Lemma lem6974401 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6974402 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem6974405 {A B : Type'} (f : A -> B) (y : A) : (term108 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6974406 {A : Type'} (f : A -> nat) (y : A) : (term109 A f y) = (f y).
Proof. exact (@lem6974405 A nat f y). Qed.
Lemma lem6974407 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term110 A s f x) = (term111 A s f x).
Proof. exact (@lem6974406 A (term98 A s f) x). Qed.
Lemma lem6974408 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term111 A s f x) = (term112 A s f x).
Proof. exact (eq_refl (term111 A s f x)). Qed.
Lemma lem6974409 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term113 A s f) = (term98 A s f).
Proof. exact (fun_ext (fun x : A => @lem6974408 A s f x)). Qed.
Lemma lem6974410 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6974411 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term110 A s f x) = (term111 A s f x).
Proof. exact (MK_COMB (@lem6974409 A s f) (@lem6974410 A x)). Qed.
Lemma lem6974412 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6974413 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term114 A s f x) = (term115 A s f x).
Proof. exact (MK_COMB (@lem6974412) (@lem6974411 A s f x)). Qed.
Lemma lem6974414 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term111 A s f x) = (term112 A s f x).
Proof. exact (eq_refl (term111 A s f x)). Qed.
Lemma lem6974415 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : ((term110 A s f x) = (term111 A s f x)) = ((term111 A s f x) = (term112 A s f x)).
Proof. exact (MK_COMB (@lem6974413 A s f x) (@lem6974414 A s f x)). Qed.
Lemma lem6974416 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term111 A s f x) = (term112 A s f x).
Proof. exact (EQ_MP (@lem6974415 A s f x) (@lem6974407 A s f x)). Qed.
Lemma lem6974417 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6974418 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term116 A s f x) = (term117 A s f x).
Proof. exact (MK_COMB (@lem6974417) (@lem6974416 A s f x)). Qed.
Lemma lem6974419 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6974420 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term101 A s f x b) = (term55 A s f x b).
Proof. exact (MK_COMB (@lem6974418 A s f x) (@lem6974419 b)). Qed.
Lemma lem6974422 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term118 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem6974365 A f b x s h1 h0). Qed.
Lemma lem6974423 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term118 A s f x b.
Proof. exact (@lem6974422 A x s f b h1). Qed.
Lemma lem6974425 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem6974402 A x s) (@lem6974401 A x s h1)). Qed.
Lemma lem6974426 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem6974425 A x s h1)). Qed.
Lemma lem6974427 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem6974426 A x s h1) (@lem0)). Qed.
Lemma lem6974428 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @IN A x s) : (term55 A s f x b) = True.
Proof. exact (@lem6974423 A x s f b h1 (@lem6974427 A x s h2)). Qed.
Lemma lem6974429 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @IN A x s) : (term101 A s f x b) = True.
Proof. exact (TRANS (@lem6974420 A s f x b) (@lem6974428 A f b x s h1 h2)). Qed.
Lemma lem6974430 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : term119 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem6974429 A f b x s h1 h0). Qed.
Lemma lem6974431 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : term120 A f b x s.
Proof. exact (@lem6974400 A f b x s True). Qed.
Lemma lem6974432 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : (term121 A s f x b) = (term122 A x s).
Proof. exact (@lem6974431 A f b x s (@lem6974430 A x s f b h1)). Qed.
Lemma lem6974434 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6974435 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = True.
Proof. exact (@lem6974434 (@IN A x s)). Qed.
Lemma lem6974436 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : (term121 A s f x b) = True.
Proof. exact (TRANS (@lem6974432 A x s f b h1) (@lem6974435 A x s)). Qed.
Lemma lem6974437 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : (term123 A s f b) = (term124 A).
Proof. exact (fun_ext (fun x : A => @lem6974436 A x s f b h1)). Qed.
Lemma lem6974438 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6974439 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : (term125 A s f b) = (term126 A).
Proof. exact (MK_COMB (@lem6974438 A) (@lem6974437 A s f b h1)). Qed.
Lemma lem6974441 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6974442 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (@lem6974441 A t). Qed.
Lemma lem6974443 {A : Type'} : (term126 A) = True.
Proof. exact (@lem6974442 A True). Qed.
Lemma lem6974444 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term62 A s f b) : (term125 A s f b) = True.
Proof. exact (TRANS (@lem6974439 A s f b h1) (@lem6974443 A)). Qed.
Lemma lem6974445 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : (term128 A s f b) = (True /\ True).
Proof. exact (MK_COMB (@lem6974380 A s h2) (@lem6974444 A s f b h1)). Qed.
Lemma lem6974447 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6974448 : (True /\ True) = True.
Proof. exact (@lem6974447 True). Qed.
Lemma lem6974449 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : (term128 A s f b) = True.
Proof. exact (TRANS (@lem6974445 A f b s h1 h2) (@lem6974448)). Qed.
Lemma lem6974450 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : True = (term128 A s f b).
Proof. exact (SYM (@lem6974449 A f b s h1 h2)). Qed.
Lemma lem6974451 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : term128 A s f b.
Proof. exact (EQ_MP (@lem6974450 A f b s h1 h2) (@lem0)). Qed.
Lemma lem6974452 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : (term86 A f s b) = True.
Proof. exact (@lem6974374 A f s b (@lem6974451 A f b s h1 h2)). Qed.
Lemma lem6974453 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : True = (term86 A f s b).
Proof. exact (SYM (@lem6974452 A f b s h1 h2)). Qed.
Lemma lem6974454 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) : term86 A f s b.
Proof. exact (EQ_MP (@lem6974453 A f b s h1 h2) (@lem0)). Qed.
Lemma lem6974455 {_99911 : Type'} (s : _99911 -> Prop) : term9 _99911 s.
Proof. exact (@lem3854502 _99911 s). Qed.
Lemma lem6974456 {_99911 : Type'} (s : _99911 -> Prop) : (term9 _99911 s) = (term10 _99911 s).
Proof. exact (eq_refl (term9 _99911 s)). Qed.
Lemma lem6974457 {_99911 : Type'} (s : _99911 -> Prop) : term10 _99911 s.
Proof. exact (EQ_MP (@lem6974456 _99911 s) (@lem6974455 _99911 s)). Qed.
Lemma lem6974458 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : @FINITE _99911 s.
Proof. exact (h1). Qed.
Lemma lem6974459 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : ((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911)).
Proof. exact (@lem6974457 _99911 s (@lem6974458 _99911 s h1)). Qed.
Lemma lem6974465 (m : nat) : term129 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem6974466 (m : nat) : (term129 m) = (term130 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem6974467 (m : nat) : term130 m.
Proof. exact (EQ_MP (@lem6974466 m) (@lem6974465 m)). Qed.
Lemma lem6974468 (m : nat) (n : nat) : term131 m n.
Proof. exact (@lem6974467 m n). Qed.
Lemma lem6974469 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem6974470 (m : nat) (n : nat) : term132 m n.
Proof. exact (EQ_MP (@lem6974469 m n) (@lem6974468 m n)). Qed.
Lemma lem6974471 (m : nat) (n : nat) (p : nat) : term133 m n p.
Proof. exact (@lem6974470 m n p). Qed.
Lemma lem6974472 (m : nat) (n : nat) (p : nat) : (term133 m n p) = ((term134 n m p) = (term135 m n p)).
Proof. exact (eq_refl (term133 m n p)). Qed.
Lemma lem6974474 {A : Type'} (f : A -> nat) : term136 A f.
Proof. exact (@lem6932066 A f). Qed.
Lemma lem6974475 {A : Type'} (f : A -> nat) : (term136 A f) = (term137 A f).
Proof. exact (eq_refl (term136 A f)). Qed.
Lemma lem6974476 {A : Type'} (f : A -> nat) : term137 A f.
Proof. exact (EQ_MP (@lem6974475 A f) (@lem6974474 A f)). Qed.
Lemma lem6974477 {A : Type'} (f : A -> nat) (c : nat) : term138 A f c.
Proof. exact (@lem6974476 A f c). Qed.
Lemma lem6974478 {A : Type'} (c : nat) (f : A -> nat) : (term138 A f c) = (term139 A c f).
Proof. exact (eq_refl (term138 A f c)). Qed.
Lemma lem6974479 {A : Type'} (c : nat) (f : A -> nat) : term139 A c f.
Proof. exact (EQ_MP (@lem6974478 A c f) (@lem6974477 A f c)). Qed.
Lemma lem6974480 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : term140 A c f s.
Proof. exact (@lem6974479 A c f s). Qed.
Lemma lem6974481 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term140 A c f s) = ((term141 A s c f) = (term142 A c s f)).
Proof. exact (eq_refl (term140 A c f s)). Qed.
Lemma lem6974483 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6974485 {A : Type'} (s : A -> Prop) : term39 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem6974513 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6974514 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6974513 p q p' q'). Qed.
Lemma lem6974515 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6974514 p q p'). Qed.
Lemma lem6974516 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term143 A s f b.
Proof. exact (@lem6974515 (term86 A f s b) (term16 A s f b)). Qed.
Lemma lem6974517 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term144 A s f b p'.
Proof. exact (@lem6974516 A s f b p'). Qed.
Lemma lem6974518 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : (term144 A s f b p') = (term145 A s f b p').
Proof. exact (eq_refl (term144 A s f b p')). Qed.
Lemma lem6974519 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) : term145 A s f b p'.
Proof. exact (EQ_MP (@lem6974518 A s f b p') (@lem6974517 A s f b p')). Qed.
Lemma lem6974520 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term146 A s f b p' q'.
Proof. exact (@lem6974519 A s f b p' q'). Qed.
Lemma lem6974521 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : (term146 A s f b p' q') = (term147 A s f b p' q').
Proof. exact (eq_refl (term146 A s f b p' q')). Qed.
Lemma lem6974522 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (p' : Prop) (q' : Prop) : term147 A s f b p' q'.
Proof. exact (EQ_MP (@lem6974521 A s f b p' q') (@lem6974520 A s f b p' q')). Qed.
Lemma lem6974524 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term141 A s c f) = (term142 A c s f).
Proof. exact (EQ_MP (@lem6974481 A c s f) (@lem6974480 A c f s)). Qed.
Lemma lem6974525 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term141 A s c f) = (term142 A c s f).
Proof. exact (@lem6974524 A c s f). Qed.
Lemma lem6974526 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term148 A s f) = (term149 A s f).
Proof. exact (@lem6974525 A (@CARD A s) s f). Qed.
Lemma lem6974527 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6974528 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term150 A s f) = (term151 A s f).
Proof. exact (MK_COMB (@lem6974527) (@lem6974526 A s f)). Qed.
Lemma lem6974529 {A : Type'} (s : A -> Prop) (b : nat) : (term152 A s b) = (term152 A s b).
Proof. exact (eq_refl (term152 A s b)). Qed.
Lemma lem6974530 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term86 A f s b) = (term153 A f s b).
Proof. exact (MK_COMB (@lem6974528 A s f) (@lem6974529 A s b)). Qed.
Lemma lem6974532 (m : nat) (n : nat) (p : nat) : (term134 n m p) = (term135 m n p).
Proof. exact (EQ_MP (@lem6974472 m n p) (@lem6974471 m n p)). Qed.
Lemma lem6974533 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term153 A f s b) = (term154 A s f b).
Proof. exact (@lem6974532 (@CARD A s) (@nsum A s f) b). Qed.
Lemma lem6974537 {_99911 : Type'} (s : _99911 -> Prop) : term10 _99911 s.
Proof. exact (fun h0 : @FINITE _99911 s => @lem6974459 _99911 s h0). Qed.
Lemma lem6974538 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem6974537 A s). Qed.
Lemma lem6974540 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6974483 A s) (@lem6974322 A s h1)). Qed.
Lemma lem6974541 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6974540 A s h1)). Qed.
Lemma lem6974542 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6974541 A s h1) (@lem0)). Qed.
Lemma lem6974543 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : ((@CARD A s) = (NUMERAL 0)) = (s = (@EMPTY A)).
Proof. exact (@lem6974538 A s (@lem6974542 A s h1)). Qed.
Lemma lem6974545 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem6974485 A s (@lem6974323 A s h1)). Qed.
Lemma lem6974546 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : ((@CARD A s) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem6974543 A s h1) (@lem6974545 A s h2)). Qed.
Lemma lem6974547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6974548 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term155 A s) = (or False).
Proof. exact (MK_COMB (@lem6974547) (@lem6974546 A s h1 h2)). Qed.
Lemma lem6974549 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term16 A s f b) = (term16 A s f b).
Proof. exact (eq_refl (term16 A s f b)). Qed.
Lemma lem6974550 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term154 A s f b) = (term156 A s f b).
Proof. exact (MK_COMB (@lem6974548 A s h1 h2) (@lem6974549 A s f b)). Qed.
Lemma lem6974552 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem6974553 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term156 A s f b) = (term16 A s f b).
Proof. exact (@lem6974552 (term16 A s f b)). Qed.
Lemma lem6974554 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term154 A s f b) = (term16 A s f b).
Proof. exact (TRANS (@lem6974550 A f b s h1 h2) (@lem6974553 A s f b)). Qed.
Lemma lem6974555 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term153 A f s b) = (term16 A s f b).
Proof. exact (TRANS (@lem6974533 A s f b) (@lem6974554 A f b s h1 h2)). Qed.
Lemma lem6974556 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term86 A f s b) = (term16 A s f b).
Proof. exact (TRANS (@lem6974530 A f s b) (@lem6974555 A f b s h1 h2)). Qed.
Lemma lem6974557 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (q' : Prop) : term157 A s f b q'.
Proof. exact (@lem6974522 A s f b (term16 A s f b) q'). Qed.
Lemma lem6974558 {A : Type'} (f : A -> nat) (b : nat) (q' : Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term158 A s f b q'.
Proof. exact (@lem6974557 A s f b q' (@lem6974556 A f b s h1 h2)). Qed.
Lemma lem6974559 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term16 A s f b) : term16 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974560 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term16 A s f b) = ((term16 A s f b) = True).
Proof. exact (@lem7 (term16 A s f b)). Qed.
Lemma lem6974563 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term16 A s f b) : (term16 A s f b) = True.
Proof. exact (EQ_MP (@lem6974560 A s f b) (@lem6974559 A s f b h1)). Qed.
Lemma lem6974564 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term159 A s f b.
Proof. exact (fun h0 : term16 A s f b => @lem6974563 A s f b h0). Qed.
Lemma lem6974565 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term160 A s f b.
Proof. exact (@lem6974558 A f b True s h1 h2). Qed.
Lemma lem6974566 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term161 A s f b) = (term162 A s f b).
Proof. exact (@lem6974565 A f b s h1 h2 (@lem6974564 A s f b)). Qed.
Lemma lem6974568 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6974569 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term162 A s f b) = True.
Proof. exact (@lem6974568 (term16 A s f b)). Qed.
Lemma lem6974570 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term161 A s f b) = True.
Proof. exact (TRANS (@lem6974566 A f b s h1 h2) (@lem6974569 A s f b)). Qed.
Lemma lem6974571 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : True = (term161 A s f b).
Proof. exact (SYM (@lem6974570 A f b s h1 h2)). Qed.
Lemma lem6974572 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term161 A s f b.
Proof. exact (EQ_MP (@lem6974571 A f b s h1 h2) (@lem0)). Qed.
Lemma lem6974573 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (h1 : @FINITE A s) (h2 : term29 A s) (h3 : term86 A f s b) : term16 A s f b.
Proof. exact (@lem6974572 A f b s h1 h2 (@lem6974325 A f s b h3)). Qed.
Lemma lem6974574 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) (h3 : term29 A s) : (term86 A f s b) = (term16 A s f b).
Proof. exact (prop_ext (fun h4 : term86 A f s b => @lem6974573 A f s b h2 h3 h4) (fun h4 : term16 A s f b => @lem6974454 A f b s h1 h2)). Qed.
Lemma lem6974575 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) (h3 : term29 A s) : term16 A s f b.
Proof. exact (EQ_MP (@lem6974574 A f b s h1 h2 h3) (@lem6974454 A f b s h1 h2)). Qed.
Lemma lem6974576 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) (h3 : term29 A s) : (term62 A s f b) = (term16 A s f b).
Proof. exact (prop_ext (fun h4 : term62 A s f b => @lem6974575 A f b s h1 h2 h3) (fun h4 : term16 A s f b => @lem6974324 A s f b h1)). Qed.
Lemma lem6974577 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term62 A s f b) (h2 : @FINITE A s) (h3 : term29 A s) : term16 A s f b.
Proof. exact (EQ_MP (@lem6974576 A f b s h1 h2 h3) (@lem6974324 A s f b h1)). Qed.
Lemma lem6974578 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term67 A s f b.
Proof. exact (fun h0 : term62 A s f b => @lem6974577 A f b s h0 h1 h2). Qed.
Lemma lem6974579 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : (term29 A s) = (term67 A s f b).
Proof. exact (prop_ext (fun h3 : term29 A s => @lem6974578 A f b s h1 h2) (fun h3 : term67 A s f b => @lem6974323 A s h2)). Qed.
Lemma lem6974580 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term29 A s) : term67 A s f b.
Proof. exact (EQ_MP (@lem6974579 A f b s h1 h2) (@lem6974323 A s h2)). Qed.
Lemma lem6974581 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : term70 A s f b.
Proof. exact (fun h0 : term29 A s => @lem6974580 A f b s h1 h0). Qed.
Lemma lem6974582 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = (term70 A s f b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6974581 A f b s h1) (fun h2 : term70 A s f b => @lem6974322 A s h1)). Qed.
Lemma lem6974583 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : term70 A s f b.
Proof. exact (EQ_MP (@lem6974582 A f b s h1) (@lem6974322 A s h1)). Qed.
Lemma lem6974584 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term73 A s f b.
Proof. exact (fun h0 : @FINITE A s => @lem6974583 A f b s h0). Qed.
Lemma lem6974589 {A : Type'} (s : A -> Prop) (f : A -> nat) : term77 A s f.
Proof. exact (fun b : nat => @lem6974584 A s f b). Qed.
Lemma lem6974594 {A : Type'} (s : A -> Prop) : term81 A s.
Proof. exact (fun f : A -> nat => @lem6974589 A s f). Qed.
Lemma lem6974599 {A : Type'} : term85 A.
Proof. exact (fun s : A -> Prop => @lem6974594 A s). Qed.
Lemma lem6974600 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem6974321 A) (@lem6974599 A)). Qed.
