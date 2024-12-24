Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_NSUM_MOD_term_abbrevs.
Require Import ETA_AX_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import MOD_ADD_MOD_spec.
Require Import MOD_MOD_REFL_spec.
Require Import MOD_ZERO_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7052566 (m : nat) : term0 m.
Proof. exact (@lem183010 m). Qed.
Lemma lem7052567 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7052568 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7052567 m) (@lem7052566 m)). Qed.
Lemma lem7052569 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7052568 m n). Qed.
Lemma lem7052570 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7052575 (a : nat) (b : nat) (n : nat) (h1 : (term4 a b n) = (term5 a b n)) : (term4 a b n) = (term5 a b n).
Proof. exact (h1). Qed.
Lemma lem7052576 (a : nat) (b : nat) (n : nat) (h1 : (term4 a b n) = (term5 a b n)) : (term5 a b n) = (term4 a b n).
Proof. exact (SYM (@lem7052575 a b n h1)). Qed.
Lemma lem7052577 (a : nat) (b : nat) (n : nat) (h1 : (term5 a b n) = (term4 a b n)) : (term5 a b n) = (term4 a b n).
Proof. exact (h1). Qed.
Lemma lem7052578 (a : nat) (b : nat) (n : nat) (h1 : (term5 a b n) = (term4 a b n)) : (term4 a b n) = (term5 a b n).
Proof. exact (SYM (@lem7052577 a b n h1)). Qed.
Lemma lem7052579 (a : nat) (b : nat) (n : nat) : ((term4 a b n) = (term5 a b n)) = ((term5 a b n) = (term4 a b n)).
Proof. exact (prop_ext (fun h1 : (term4 a b n) = (term5 a b n) => @lem7052576 a b n h1) (fun h1 : (term5 a b n) = (term4 a b n) => @lem7052578 a b n h1)). Qed.
Lemma lem7052580 (a : nat) (b : nat) : (term6 a b) = (term7 a b).
Proof. exact (fun_ext (fun n : nat => @lem7052579 a b n)). Qed.
Lemma lem7052581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052582 (a : nat) (b : nat) : (term8 a b) = (term9 a b).
Proof. exact (MK_COMB (@lem7052581) (@lem7052580 a b)). Qed.
Lemma lem7052583 (a : nat) : (term10 a) = (term11 a).
Proof. exact (fun_ext (fun b : nat => @lem7052582 a b)). Qed.
Lemma lem7052584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052585 (a : nat) : (term12 a) = (term13 a).
Proof. exact (MK_COMB (@lem7052584) (@lem7052583 a)). Qed.
Lemma lem7052586 : term14 = term15.
Proof. exact (fun_ext (fun a : nat => @lem7052585 a)). Qed.
Lemma lem7052587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052588 : term16 = term17.
Proof. exact (MK_COMB (@lem7052587) (@lem7052586)). Qed.
Lemma lem7052589 : term17.
Proof. exact (EQ_MP (@lem7052588) (@lem209995)). Qed.
Lemma lem7052590 (a : nat) : term18 a.
Proof. exact (@lem7052589 a). Qed.
Lemma lem7052591 (a : nat) : (term18 a) = (term13 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem7052592 (a : nat) : term13 a.
Proof. exact (EQ_MP (@lem7052591 a) (@lem7052590 a)). Qed.
Lemma lem7052593 (a : nat) (b : nat) : term19 a b.
Proof. exact (@lem7052592 a b). Qed.
Lemma lem7052594 (a : nat) (b : nat) : (term19 a b) = (term9 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem7052595 (a : nat) (b : nat) : term9 a b.
Proof. exact (EQ_MP (@lem7052594 a b) (@lem7052593 a b)). Qed.
Lemma lem7052596 (a : nat) (b : nat) (n : nat) : term20 a b n.
Proof. exact (@lem7052595 a b n). Qed.
Lemma lem7052597 (a : nat) (b : nat) (n : nat) : (term20 a b n) = ((term5 a b n) = (term4 a b n)).
Proof. exact (eq_refl (term20 a b n)). Qed.
Lemma lem7052602 (a : nat) (b : nat) (n : nat) (h1 : (term4 a b n) = (term5 a b n)) : (term4 a b n) = (term5 a b n).
Proof. exact (h1). Qed.
Lemma lem7052603 (a : nat) (b : nat) (n : nat) (h1 : (term4 a b n) = (term5 a b n)) : (term5 a b n) = (term4 a b n).
Proof. exact (SYM (@lem7052602 a b n h1)). Qed.
Lemma lem7052604 (a : nat) (b : nat) (n : nat) (h1 : (term5 a b n) = (term4 a b n)) : (term5 a b n) = (term4 a b n).
Proof. exact (h1). Qed.
Lemma lem7052605 (a : nat) (b : nat) (n : nat) (h1 : (term5 a b n) = (term4 a b n)) : (term4 a b n) = (term5 a b n).
Proof. exact (SYM (@lem7052604 a b n h1)). Qed.
Lemma lem7052606 (a : nat) (b : nat) (n : nat) : ((term4 a b n) = (term5 a b n)) = ((term5 a b n) = (term4 a b n)).
Proof. exact (prop_ext (fun h1 : (term4 a b n) = (term5 a b n) => @lem7052603 a b n h1) (fun h1 : (term5 a b n) = (term4 a b n) => @lem7052605 a b n h1)). Qed.
Lemma lem7052607 (a : nat) (b : nat) : (term6 a b) = (term7 a b).
Proof. exact (fun_ext (fun n : nat => @lem7052606 a b n)). Qed.
Lemma lem7052608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052609 (a : nat) (b : nat) : (term8 a b) = (term9 a b).
Proof. exact (MK_COMB (@lem7052608) (@lem7052607 a b)). Qed.
Lemma lem7052610 (a : nat) : (term10 a) = (term11 a).
Proof. exact (fun_ext (fun b : nat => @lem7052609 a b)). Qed.
Lemma lem7052611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052612 (a : nat) : (term12 a) = (term13 a).
Proof. exact (MK_COMB (@lem7052611) (@lem7052610 a)). Qed.
Lemma lem7052613 : term14 = term15.
Proof. exact (fun_ext (fun a : nat => @lem7052612 a)). Qed.
Lemma lem7052614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052615 : term16 = term17.
Proof. exact (MK_COMB (@lem7052614) (@lem7052613)). Qed.
Lemma lem7052616 : term17.
Proof. exact (EQ_MP (@lem7052615) (@lem209995)). Qed.
Lemma lem7052617 (a : nat) : term18 a.
Proof. exact (@lem7052616 a). Qed.
Lemma lem7052618 (a : nat) : (term18 a) = (term13 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem7052619 (a : nat) : term13 a.
Proof. exact (EQ_MP (@lem7052618 a) (@lem7052617 a)). Qed.
Lemma lem7052620 (a : nat) (b : nat) : term19 a b.
Proof. exact (@lem7052619 a b). Qed.
Lemma lem7052621 (a : nat) (b : nat) : (term19 a b) = (term9 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem7052622 (a : nat) (b : nat) : term9 a b.
Proof. exact (EQ_MP (@lem7052621 a b) (@lem7052620 a b)). Qed.
Lemma lem7052623 (a : nat) (b : nat) (n : nat) : term20 a b n.
Proof. exact (@lem7052622 a b n). Qed.
Lemma lem7052624 (a : nat) (b : nat) (n : nat) : (term20 a b n) = ((term5 a b n) = (term4 a b n)).
Proof. exact (eq_refl (term20 a b n)). Qed.
Lemma lem7052626 {_126525 : Type'} : term21 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem7052627 {_126525 : Type'} (x : _126525) : term22 _126525 x.
Proof. exact (@lem7052626 _126525 x). Qed.
Lemma lem7052628 {_126525 : Type'} (x : _126525) : (term22 _126525 x) = (term23 _126525 x).
Proof. exact (eq_refl (term22 _126525 x)). Qed.
Lemma lem7052629 {_126525 : Type'} (x : _126525) : term23 _126525 x.
Proof. exact (EQ_MP (@lem7052628 _126525 x) (@lem7052627 _126525 x)). Qed.
Lemma lem7052630 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term24 _126525 x f.
Proof. exact (@lem7052629 _126525 x f). Qed.
Lemma lem7052631 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term24 _126525 x f) = (term25 _126525 x f).
Proof. exact (eq_refl (term24 _126525 x f)). Qed.
Lemma lem7052632 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term25 _126525 x f.
Proof. exact (EQ_MP (@lem7052631 _126525 x f) (@lem7052630 _126525 x f)). Qed.
Lemma lem7052633 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term26 _126525 x f s.
Proof. exact (@lem7052632 _126525 x f s). Qed.
Lemma lem7052634 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term26 _126525 x f s) = (term27 _126525 x s f).
Proof. exact (eq_refl (term26 _126525 x f s)). Qed.
Lemma lem7052635 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term27 _126525 x s f.
Proof. exact (EQ_MP (@lem7052634 _126525 x s f) (@lem7052633 _126525 x f s)). Qed.
Lemma lem7052636 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem7052637 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term28 _126525 x s f) = (term29 _126525 x s f).
Proof. exact (@lem7052635 _126525 x s f (@lem7052636 _126525 s h1)). Qed.
Lemma lem7052643 {_126486 : Type'} : term30 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem7052644 {_126486 : Type'} (f : _126486 -> nat) : term31 _126486 f.
Proof. exact (@lem7052643 _126486 f). Qed.
Lemma lem7052645 {_126486 : Type'} (f : _126486 -> nat) : (term31 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term31 _126486 f)). Qed.
Lemma lem7052647 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem7052648 {A : Type'} (P : type686 A) (h1 : term32 A) : term33 A P.
Proof. exact (@lem7052647 A h1 P). Qed.
Lemma lem7052649 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem7052650 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (EQ_MP (@lem7052649 A P) (@lem7052648 A P h1)). Qed.
Lemma lem7052651 {A : Type'} (P : type686 A) (h1 : term35 A P) : term35 A P.
Proof. exact (h1). Qed.
Lemma lem7052652 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem7052650 A P h1 (@lem7052651 A P h2)). Qed.
Lemma lem7052653 {A : Type'} (P : type686 A) (h1 : term35 A P) : term37 A P.
Proof. exact (fun h0 : term32 A => @lem7052652 A P h0 h1). Qed.
Lemma lem7052654 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem7052655 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem7052653 A P h2 (@lem7052654 A h1)). Qed.
Lemma lem7052656 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (fun h0 : term35 A P => @lem7052655 A P h1 h0). Qed.
Lemma lem7052657 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (fun P : type686 A => @lem7052656 A P h1). Qed.
Lemma lem7052658 {A : Type'} : term38 A.
Proof. exact (fun h0 : term32 A => @lem7052657 A h0). Qed.
Lemma lem7052659 {A : Type'} : term32 A.
Proof. exact (@lem7052658 A (@lem3558722 A)). Qed.
Lemma lem7052660 {A : Type'} (P : type686 A) : term33 A P.
Proof. exact (@lem7052659 A P). Qed.
Lemma lem7052661 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem7052663 (n : nat) : term39 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem7052664 (n : nat) : (term39 n) = (term40 n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem7052665 (n : nat) : term40 n.
Proof. exact (EQ_MP (@lem7052664 n) (@lem7052663 n)). Qed.
Lemma lem7052668 {A B : Type'} (t : A -> B) : term41 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem7052669 {A B : Type'} (t : A -> B) : (term41 A B t) = ((term42 A B t) = t).
Proof. exact (eq_refl (term41 A B t)). Qed.
Lemma lem7052670 {A B : Type'} (t : A -> B) : (term42 A B t) = t.
Proof. exact (EQ_MP (@lem7052669 A B t) (@lem7052668 A B t)). Qed.
Lemma lem7052671 (n : nat) : term43 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem7052672 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem7052683 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7052684 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term45 A s f) = (term45 A s f).
Proof. exact (eq_refl (term45 A s f)). Qed.
Lemma lem7052685 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term46 A s f n) = (term47 A s f).
Proof. exact (MK_COMB (@lem7052684 A s f) (@lem7052683 n h1)). Qed.
Lemma lem7052687 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem7052672 n) (@lem7052671 n)). Qed.
Lemma lem7052688 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term47 A s f) = (@nsum A s f).
Proof. exact (@lem7052687 (@nsum A s f)). Qed.
Lemma lem7052689 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term46 A s f n) = (@nsum A s f).
Proof. exact (TRANS (@lem7052685 A s f n h1) (@lem7052688 A s f)). Qed.
Lemma lem7052690 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052691 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term48 A s f n) = (term49 A s f).
Proof. exact (MK_COMB (@lem7052690) (@lem7052689 A s f n h1)). Qed.
Lemma lem7052693 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7052694 {A : Type'} (f : A -> nat) (i : A) : (term50 A f i) = (term50 A f i).
Proof. exact (eq_refl (term50 A f i)). Qed.
Lemma lem7052695 {A : Type'} (f : A -> nat) (i : A) (n : nat) (h1 : n = (NUMERAL 0)) : (term51 A f i n) = (term52 A f i).
Proof. exact (MK_COMB (@lem7052694 A f i) (@lem7052693 n h1)). Qed.
Lemma lem7052697 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem7052672 n) (@lem7052671 n)). Qed.
Lemma lem7052698 {A : Type'} (f : A -> nat) (i : A) : (term52 A f i) = (f i).
Proof. exact (@lem7052697 (f i)). Qed.
Lemma lem7052699 {A : Type'} (f : A -> nat) (i : A) (n : nat) (h1 : n = (NUMERAL 0)) : (term51 A f i n) = (f i).
Proof. exact (TRANS (@lem7052695 A f i n h1) (@lem7052698 A f i)). Qed.
Lemma lem7052700 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term53 A f n) = (term54 A f).
Proof. exact (fun_ext (fun i : A => @lem7052699 A f i n h1)). Qed.
Lemma lem7052701 {A : Type'} (t : A -> nat) : (term54 A t) = t.
Proof. exact (@lem7052670 A nat t). Qed.
Lemma lem7052702 {A : Type'} (f : A -> nat) : (term54 A f) = f.
Proof. exact (@lem7052701 A f). Qed.
Lemma lem7052703 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term53 A f n) = f.
Proof. exact (TRANS (@lem7052700 A f n h1) (@lem7052702 A f)). Qed.
Lemma lem7052704 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem7052705 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term55 A s f n) = (@nsum A s f).
Proof. exact (MK_COMB (@lem7052704 A s) (@lem7052703 A f n h1)). Qed.
Lemma lem7052706 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7052707 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term56 A s f n) = (term45 A s f).
Proof. exact (MK_COMB (@lem7052706) (@lem7052705 A s f n h1)). Qed.
Lemma lem7052709 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7052710 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term57 A s f n) = (term47 A s f).
Proof. exact (MK_COMB (@lem7052707 A s f n h1) (@lem7052709 n h1)). Qed.
Lemma lem7052712 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem7052672 n) (@lem7052671 n)). Qed.
Lemma lem7052713 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term47 A s f) = (@nsum A s f).
Proof. exact (@lem7052712 (@nsum A s f)). Qed.
Lemma lem7052714 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term57 A s f n) = (@nsum A s f).
Proof. exact (TRANS (@lem7052710 A s f n h1) (@lem7052713 A s f)). Qed.
Lemma lem7052715 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term46 A s f n) = (term57 A s f n)) = ((@nsum A s f) = (@nsum A s f)).
Proof. exact (MK_COMB (@lem7052691 A s f n h1) (@lem7052714 A s f n h1)). Qed.
Lemma lem7052717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7052718 (x : nat) : (x = x) = True.
Proof. exact (@lem7052717 nat x). Qed.
Lemma lem7052719 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((@nsum A s f) = (@nsum A s f)) = True.
Proof. exact (@lem7052718 (@nsum A s f)). Qed.
Lemma lem7052720 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term46 A s f n) = (term57 A s f n)) = True.
Proof. exact (TRANS (@lem7052715 A s f n h1) (@lem7052719 A s f)). Qed.
Lemma lem7052721 {A : Type'} (s : A -> Prop) : (term58 A s) = (term58 A s).
Proof. exact (eq_refl (term58 A s)). Qed.
Lemma lem7052722 {A : Type'} (f : A -> nat) (s : A -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term59 A s f n) = (term60 A s).
Proof. exact (MK_COMB (@lem7052721 A s) (@lem7052720 A s f n h1)). Qed.
Lemma lem7052724 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7052725 {A : Type'} (s : A -> Prop) : (term60 A s) = True.
Proof. exact (@lem7052724 (@FINITE A s)). Qed.
Lemma lem7052726 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term59 A s f n) = True.
Proof. exact (TRANS (@lem7052722 A f s n h1) (@lem7052725 A s)). Qed.
Lemma lem7052727 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term61 A f n) = (term62 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7052726 A s f n h1)). Qed.
Lemma lem7052728 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7052729 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term63 A f n) = (term64 A).
Proof. exact (MK_COMB (@lem7052728 A) (@lem7052727 A f n h1)). Qed.
Lemma lem7052731 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7052732 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (@lem7052731 (A -> Prop) t). Qed.
Lemma lem7052733 {A : Type'} : (term64 A) = True.
Proof. exact (@lem7052732 A True). Qed.
Lemma lem7052734 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term63 A f n) = True.
Proof. exact (TRANS (@lem7052729 A f n h1) (@lem7052733 A)). Qed.
Lemma lem7052735 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term63 A f n).
Proof. exact (SYM (@lem7052734 A f n h1)). Qed.
Lemma lem7052736 {A : Type'} (f : A -> nat) (n : nat) (h1 : n = (NUMERAL 0)) : term63 A f n.
Proof. exact (EQ_MP (@lem7052735 A f n h1) (@lem0)). Qed.
Lemma lem7052767 {A : Type'} (P : type686 A) : term34 A P.
Proof. exact (EQ_MP (@lem7052661 A P) (@lem7052660 A P)). Qed.
Lemma lem7052768 {A : Type'} (P : type686 A) : term34 A P.
Proof. exact (@lem7052767 A P). Qed.
Lemma lem7052769 {A : Type'} (f : A -> nat) (n : nat) : term67 A f n.
Proof. exact (@lem7052768 A (term68 A f n)). Qed.
Lemma lem7052770 {A : Type'} (f : A -> nat) (n : nat) : (term69 A f n) = ((term70 A f n) = (term71 A f n)).
Proof. exact (eq_refl (term69 A f n)). Qed.
Lemma lem7052771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7052772 {A : Type'} (f : A -> nat) (n : nat) : (term72 A f n) = (term73 A f n).
Proof. exact (MK_COMB (@lem7052771) (@lem7052770 A f n)). Qed.
Lemma lem7052773 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term74 A f n s) = ((term46 A s f n) = (term57 A s f n)).
Proof. exact (eq_refl (term74 A f n s)). Qed.
Lemma lem7052774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7052775 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term75 A f n s) = (term76 A s f n).
Proof. exact (MK_COMB (@lem7052774) (@lem7052773 A s f n)). Qed.
Lemma lem7052776 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (term77 A x s).
Proof. exact (eq_refl (term77 A x s)). Qed.
Lemma lem7052777 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) : (term78 A f n x s) = (term79 A f n x s).
Proof. exact (MK_COMB (@lem7052775 A s f n) (@lem7052776 A x s)). Qed.
Lemma lem7052778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7052779 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) : (term80 A f n x s) = (term81 A f n x s).
Proof. exact (MK_COMB (@lem7052778) (@lem7052777 A f n x s)). Qed.
Lemma lem7052780 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term82 A f n x s) = ((term83 A x s f n) = (term84 A x s f n)).
Proof. exact (eq_refl (term82 A f n x s)). Qed.
Lemma lem7052781 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term85 A f n x s) = (term86 A x s f n).
Proof. exact (MK_COMB (@lem7052779 A f n x s) (@lem7052780 A x s f n)). Qed.
Lemma lem7052782 {A : Type'} (x : A) (f : A -> nat) (n : nat) : (term87 A f n x) = (term88 A x f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7052781 A x s f n)). Qed.
Lemma lem7052783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7052784 {A : Type'} (x : A) (f : A -> nat) (n : nat) : (term89 A f n x) = (term90 A x f n).
Proof. exact (MK_COMB (@lem7052783 A) (@lem7052782 A x f n)). Qed.
Lemma lem7052785 {A : Type'} (f : A -> nat) (n : nat) : (term91 A f n) = (term92 A f n).
Proof. exact (fun_ext (fun x : A => @lem7052784 A x f n)). Qed.
Lemma lem7052786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7052787 {A : Type'} (f : A -> nat) (n : nat) : (term93 A f n) = (term94 A f n).
Proof. exact (MK_COMB (@lem7052786 A) (@lem7052785 A f n)). Qed.
Lemma lem7052788 {A : Type'} (f : A -> nat) (n : nat) : (term95 A f n) = (term96 A f n).
Proof. exact (MK_COMB (@lem7052772 A f n) (@lem7052787 A f n)). Qed.
Lemma lem7052789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7052790 {A : Type'} (f : A -> nat) (n : nat) : (term97 A f n) = (term98 A f n).
Proof. exact (MK_COMB (@lem7052789) (@lem7052788 A f n)). Qed.
Lemma lem7052791 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term74 A f n s) = ((term46 A s f n) = (term57 A s f n)).
Proof. exact (eq_refl (term74 A f n s)). Qed.
Lemma lem7052792 {A : Type'} (s : A -> Prop) : (term58 A s) = (term58 A s).
Proof. exact (eq_refl (term58 A s)). Qed.
Lemma lem7052793 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term99 A f n s) = (term59 A s f n).
Proof. exact (MK_COMB (@lem7052792 A s) (@lem7052791 A s f n)). Qed.
Lemma lem7052794 {A : Type'} (f : A -> nat) (n : nat) : (term100 A f n) = (term61 A f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7052793 A s f n)). Qed.
Lemma lem7052795 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7052796 {A : Type'} (f : A -> nat) (n : nat) : (term101 A f n) = (term63 A f n).
Proof. exact (MK_COMB (@lem7052795 A) (@lem7052794 A f n)). Qed.
Lemma lem7052797 {A : Type'} (f : A -> nat) (n : nat) : (term67 A f n) = (term102 A f n).
Proof. exact (MK_COMB (@lem7052790 A f n) (@lem7052796 A f n)). Qed.
Lemma lem7052798 {A : Type'} (f : A -> nat) (n : nat) : term102 A f n.
Proof. exact (EQ_MP (@lem7052797 A f n) (@lem7052769 A f n)). Qed.
Lemma lem7052804 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7052645 _126486 f) (@lem7052644 _126486 f)). Qed.
Lemma lem7052805 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem7052804 A f). Qed.
Lemma lem7052806 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7052807 {A : Type'} (f : A -> nat) : (term103 A f) = term104.
Proof. exact (MK_COMB (@lem7052806) (@lem7052805 A f)). Qed.
Lemma lem7052808 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7052809 {A : Type'} (f : A -> nat) (n : nat) : (term70 A f n) = (term105 n).
Proof. exact (MK_COMB (@lem7052807 A f) (@lem7052808 n)). Qed.
Lemma lem7052810 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052811 {A : Type'} (f : A -> nat) (n : nat) : (term106 A f n) = (term107 n).
Proof. exact (MK_COMB (@lem7052810) (@lem7052809 A f n)). Qed.
Lemma lem7052813 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7052645 _126486 f) (@lem7052644 _126486 f)). Qed.
Lemma lem7052814 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem7052813 A f). Qed.
Lemma lem7052815 {A : Type'} (f : A -> nat) (n : nat) : (term108 A f n) = (NUMERAL 0).
Proof. exact (@lem7052814 A (term53 A f n)). Qed.
Lemma lem7052816 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7052817 {A : Type'} (f : A -> nat) (n : nat) : (term109 A f n) = term104.
Proof. exact (MK_COMB (@lem7052816) (@lem7052815 A f n)). Qed.
Lemma lem7052818 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7052819 {A : Type'} (f : A -> nat) (n : nat) : (term71 A f n) = (term105 n).
Proof. exact (MK_COMB (@lem7052817 A f n) (@lem7052818 n)). Qed.
Lemma lem7052820 {A : Type'} (f : A -> nat) (n : nat) : ((term70 A f n) = (term71 A f n)) = ((term105 n) = (term105 n)).
Proof. exact (MK_COMB (@lem7052811 A f n) (@lem7052819 A f n)). Qed.
Lemma lem7052822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7052823 (x : nat) : (x = x) = True.
Proof. exact (@lem7052822 nat x). Qed.
Lemma lem7052824 (n : nat) : ((term105 n) = (term105 n)) = True.
Proof. exact (@lem7052823 (term105 n)). Qed.
Lemma lem7052825 {A : Type'} (f : A -> nat) (n : nat) : ((term70 A f n) = (term71 A f n)) = True.
Proof. exact (TRANS (@lem7052820 A f n) (@lem7052824 n)). Qed.
Lemma lem7052826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7052827 {A : Type'} (f : A -> nat) (n : nat) : (term73 A f n) = (and True).
Proof. exact (MK_COMB (@lem7052826) (@lem7052825 A f n)). Qed.
Lemma lem7052839 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term110 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7052840 (p : Prop) (q : Prop) (p' : Prop) : term111 p q p'.
Proof. exact (fun q' : Prop => @lem7052839 p q p' q'). Qed.
Lemma lem7052841 (p : Prop) (q : Prop) : term112 p q.
Proof. exact (fun p' : Prop => @lem7052840 p q p'). Qed.
Lemma lem7052842 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term113 A x s f n.
Proof. exact (@lem7052841 (term79 A f n x s) ((term83 A x s f n) = (term84 A x s f n))). Qed.
Lemma lem7052843 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) : term114 A x s f n p'.
Proof. exact (@lem7052842 A x s f n p'). Qed.
Lemma lem7052844 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) : (term114 A x s f n p') = (term115 A x s f n p').
Proof. exact (eq_refl (term114 A x s f n p')). Qed.
Lemma lem7052845 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) : term115 A x s f n p'.
Proof. exact (EQ_MP (@lem7052844 A x s f n p') (@lem7052843 A x s f n p')). Qed.
Lemma lem7052846 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) (q' : Prop) : term116 A x s f n p' q'.
Proof. exact (@lem7052845 A x s f n p' q'). Qed.
Lemma lem7052847 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) (q' : Prop) : (term116 A x s f n p' q') = (term117 A x s f n p' q').
Proof. exact (eq_refl (term116 A x s f n p' q')). Qed.
Lemma lem7052848 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (p' : Prop) (q' : Prop) : term117 A x s f n p' q'.
Proof. exact (EQ_MP (@lem7052847 A x s f n p' q') (@lem7052846 A x s f n p' q')). Qed.
Lemma lem7052855 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) : (term79 A f n x s) = (term79 A f n x s).
Proof. exact (eq_refl (term79 A f n x s)). Qed.
Lemma lem7052856 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (q' : Prop) : term118 A f n x s q'.
Proof. exact (@lem7052848 A x s f n (term79 A f n x s) q'). Qed.
Lemma lem7052857 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (q' : Prop) : term119 A f n x s q'.
Proof. exact (@lem7052856 A f n x s q' (@lem7052855 A f n x s)). Qed.
Lemma lem7052858 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term79 A f n x s.
Proof. exact (h1). Qed.
Lemma lem7052859 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term77 A x s.
Proof. exact (proj2 (@lem7052858 A f n x s h1)). Qed.
Lemma lem7052860 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : @FINITE A s.
Proof. exact (proj2 (@lem7052859 A f n x s h1)). Qed.
Lemma lem7052861 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7052863 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term120 A x s.
Proof. exact (proj1 (@lem7052859 A f n x s h1)). Qed.
Lemma lem7052864 {A : Type'} (x : A) (s : A -> Prop) : term121 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem7052870 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term27 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7052637 _126525 x f s h0). Qed.
Lemma lem7052871 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term27 A x s f.
Proof. exact (@lem7052870 A x s f). Qed.
Lemma lem7052873 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7052861 A s) (@lem7052860 A f n x s h1)). Qed.
Lemma lem7052874 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7052873 A f n x s h1)). Qed.
Lemma lem7052875 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7052874 A f n x s h1) (@lem0)). Qed.
Lemma lem7052876 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term28 A x s f) = (term29 A x s f).
Proof. exact (@lem7052871 A x s f (@lem7052875 A f n x s h1)). Qed.
Lemma lem7052878 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term122 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7052879 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term123 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7052878 _2963 g t e g' t' e'). Qed.
Lemma lem7052880 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term124 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7052879 _2963 g t e g' t'). Qed.
Lemma lem7052881 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term125 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7052880 _2963 g t e g'). Qed.
Lemma lem7052882 (g : Prop) (t : nat) (e : nat) : term126 g t e.
Proof. exact (@lem7052881 nat g t e). Qed.
Lemma lem7052883 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term127 A x s f.
Proof. exact (@lem7052882 (@IN A x s) (@nsum A s f) (term128 A x s f)). Qed.
Lemma lem7052884 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : term129 A x s f g'.
Proof. exact (@lem7052883 A x s f g'). Qed.
Lemma lem7052885 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : (term129 A x s f g') = (term130 A x s f g').
Proof. exact (eq_refl (term129 A x s f g')). Qed.
Lemma lem7052886 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) : term130 A x s f g'.
Proof. exact (EQ_MP (@lem7052885 A x s f g') (@lem7052884 A x s f g')). Qed.
Lemma lem7052887 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term131 A x s f g' t'.
Proof. exact (@lem7052886 A x s f g' t'). Qed.
Lemma lem7052888 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : (term131 A x s f g' t') = (term132 A x s f g' t').
Proof. exact (eq_refl (term131 A x s f g' t')). Qed.
Lemma lem7052889 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term132 A x s f g' t'.
Proof. exact (EQ_MP (@lem7052888 A x s f g' t') (@lem7052887 A x s f g' t')). Qed.
Lemma lem7052890 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term133 A x s f g' t' e'.
Proof. exact (@lem7052889 A x s f g' t' e'). Qed.
Lemma lem7052891 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term133 A x s f g' t' e') = (term134 A x s f g' t' e').
Proof. exact (eq_refl (term133 A x s f g' t' e')). Qed.
Lemma lem7052892 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term134 A x s f g' t' e'.
Proof. exact (EQ_MP (@lem7052891 A x s f g' t' e') (@lem7052890 A x s f g' t' e')). Qed.
Lemma lem7052894 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (@IN A x s) = False.
Proof. exact (@lem7052864 A x s (@lem7052863 A f n x s h1)). Qed.
Lemma lem7052895 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (t' : nat) (e' : nat) : term135 A x s f t' e'.
Proof. exact (@lem7052892 A x s f False t' e'). Qed.
Lemma lem7052896 {A : Type'} (t' : nat) (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term136 A x s f t' e'.
Proof. exact (@lem7052895 A x s f t' e' (@lem7052894 A f n x s h1)). Qed.
Lemma lem7052900 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@nsum A s f).
Proof. exact (eq_refl (@nsum A s f)). Qed.
Lemma lem7052901 {A : Type'} (s : A -> Prop) (f : A -> nat) : term137 A s f.
Proof. exact (fun h0 : False => @lem7052900 A s f). Qed.
Lemma lem7052902 {A : Type'} (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term138 A x s f e'.
Proof. exact (@lem7052896 A (@nsum A s f) e' f n x s h1). Qed.
Lemma lem7052903 {A : Type'} (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term139 A x s f e'.
Proof. exact (@lem7052902 A e' f n x s h1 (@lem7052901 A s f)). Qed.
Lemma lem7052909 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term128 A x s f) = (term128 A x s f).
Proof. exact (eq_refl (term128 A x s f)). Qed.
Lemma lem7052910 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term140 A x s f.
Proof. exact (fun h0 : ~ False => @lem7052909 A x s f). Qed.
Lemma lem7052911 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term141 A x s f.
Proof. exact (@lem7052903 A (term128 A x s f) f n x s h1). Qed.
Lemma lem7052912 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term29 A x s f) = (term142 A x s f).
Proof. exact (@lem7052911 A f n x s h1 (@lem7052910 A x s f)). Qed.
Lemma lem7052914 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7052915 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7052914 nat t1 t2). Qed.
Lemma lem7052916 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term142 A x s f) = (term128 A x s f).
Proof. exact (@lem7052915 (@nsum A s f) (term128 A x s f)). Qed.
Lemma lem7052917 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term29 A x s f) = (term128 A x s f).
Proof. exact (TRANS (@lem7052912 A f n x s h1) (@lem7052916 A x s f)). Qed.
Lemma lem7052918 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term28 A x s f) = (term128 A x s f).
Proof. exact (TRANS (@lem7052876 A f n x s h1) (@lem7052917 A f n x s h1)). Qed.
Lemma lem7052919 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7052920 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term143 A x s f) = (term144 A x s f).
Proof. exact (MK_COMB (@lem7052919) (@lem7052918 A f n x s h1)). Qed.
Lemma lem7052921 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7052922 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term83 A x s f n) = (term145 A x s f n).
Proof. exact (MK_COMB (@lem7052920 A f n x s h1) (@lem7052921 n)). Qed.
Lemma lem7052923 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052924 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term146 A x s f n) = (term147 A x s f n).
Proof. exact (MK_COMB (@lem7052923) (@lem7052922 A f n x s h1)). Qed.
Lemma lem7052926 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term27 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7052637 _126525 x f s h0). Qed.
Lemma lem7052927 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term27 A x s f.
Proof. exact (@lem7052926 A x s f). Qed.
Lemma lem7052928 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term148 A x s f n.
Proof. exact (@lem7052927 A x s (term53 A f n)). Qed.
Lemma lem7052930 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7052861 A s) (@lem7052860 A f n x s h1)). Qed.
Lemma lem7052931 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7052930 A f n x s h1)). Qed.
Lemma lem7052932 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7052931 A f n x s h1) (@lem0)). Qed.
Lemma lem7052933 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term149 A x s f n) = (term150 A x s f n).
Proof. exact (@lem7052928 A x s f n (@lem7052932 A f n x s h1)). Qed.
Lemma lem7052935 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term122 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7052936 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term123 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7052935 _2963 g t e g' t' e'). Qed.
Lemma lem7052937 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term124 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7052936 _2963 g t e g' t'). Qed.
Lemma lem7052938 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term125 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7052937 _2963 g t e g'). Qed.
Lemma lem7052939 (g : Prop) (t : nat) (e : nat) : term126 g t e.
Proof. exact (@lem7052938 nat g t e). Qed.
Lemma lem7052940 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term151 A x s f n.
Proof. exact (@lem7052939 (@IN A x s) (term55 A s f n) (term152 A x s f n)). Qed.
Lemma lem7052941 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) : term153 A x s f n g'.
Proof. exact (@lem7052940 A x s f n g'). Qed.
Lemma lem7052942 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) : (term153 A x s f n g') = (term154 A x s f n g').
Proof. exact (eq_refl (term153 A x s f n g')). Qed.
Lemma lem7052943 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) : term154 A x s f n g'.
Proof. exact (EQ_MP (@lem7052942 A x s f n g') (@lem7052941 A x s f n g')). Qed.
Lemma lem7052944 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) : term155 A x s f n g' t'.
Proof. exact (@lem7052943 A x s f n g' t'). Qed.
Lemma lem7052945 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) : (term155 A x s f n g' t') = (term156 A x s f n g' t').
Proof. exact (eq_refl (term155 A x s f n g' t')). Qed.
Lemma lem7052946 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) : term156 A x s f n g' t'.
Proof. exact (EQ_MP (@lem7052945 A x s f n g' t') (@lem7052944 A x s f n g' t')). Qed.
Lemma lem7052947 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term157 A x s f n g' t' e'.
Proof. exact (@lem7052946 A x s f n g' t' e'). Qed.
Lemma lem7052948 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term157 A x s f n g' t' e') = (term158 A x s f n g' t' e').
Proof. exact (eq_refl (term157 A x s f n g' t' e')). Qed.
Lemma lem7052949 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term158 A x s f n g' t' e'.
Proof. exact (EQ_MP (@lem7052948 A x s f n g' t' e') (@lem7052947 A x s f n g' t' e')). Qed.
Lemma lem7052951 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (@IN A x s) = False.
Proof. exact (@lem7052864 A x s (@lem7052863 A f n x s h1)). Qed.
Lemma lem7052952 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (t' : nat) (e' : nat) : term159 A x s f n t' e'.
Proof. exact (@lem7052949 A x s f n False t' e'). Qed.
Lemma lem7052953 {A : Type'} (t' : nat) (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term160 A x s f n t' e'.
Proof. exact (@lem7052952 A x s f n t' e' (@lem7052951 A f n x s h1)). Qed.
Lemma lem7052957 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term55 A s f n) = (term55 A s f n).
Proof. exact (eq_refl (term55 A s f n)). Qed.
Lemma lem7052958 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : term161 A s f n.
Proof. exact (fun h0 : False => @lem7052957 A s f n). Qed.
Lemma lem7052959 {A : Type'} (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term162 A x s f n e'.
Proof. exact (@lem7052953 A (term55 A s f n) e' f n x s h1). Qed.
Lemma lem7052960 {A : Type'} (e' : nat) (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term163 A x s f n e'.
Proof. exact (@lem7052959 A e' f n x s h1 (@lem7052958 A s f n)). Qed.
Lemma lem7052967 {A B : Type'} (f : A -> B) (y : A) : (term164 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7052968 {A : Type'} (f : A -> nat) (y : A) : (term165 A f y) = (f y).
Proof. exact (@lem7052967 A nat f y). Qed.
Lemma lem7052969 {A : Type'} (f : A -> nat) (n : nat) (x : A) : (term166 A f n x) = (term167 A f n x).
Proof. exact (@lem7052968 A (term53 A f n) x). Qed.
Lemma lem7052970 {A : Type'} (f : A -> nat) (i : A) (n : nat) : (term167 A f n i) = (term51 A f i n).
Proof. exact (eq_refl (term167 A f n i)). Qed.
Lemma lem7052971 {A : Type'} (f : A -> nat) (n : nat) : (term168 A f n) = (term53 A f n).
Proof. exact (fun_ext (fun i : A => @lem7052970 A f i n)). Qed.
Lemma lem7052972 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7052973 {A : Type'} (f : A -> nat) (n : nat) (x : A) : (term166 A f n x) = (term167 A f n x).
Proof. exact (MK_COMB (@lem7052971 A f n) (@lem7052972 A x)). Qed.
Lemma lem7052974 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052975 {A : Type'} (f : A -> nat) (n : nat) (x : A) : (term169 A f n x) = (term170 A f n x).
Proof. exact (MK_COMB (@lem7052974) (@lem7052973 A f n x)). Qed.
Lemma lem7052976 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term167 A f n x) = (term51 A f x n).
Proof. exact (eq_refl (term167 A f n x)). Qed.
Lemma lem7052977 {A : Type'} (f : A -> nat) (x : A) (n : nat) : ((term166 A f n x) = (term167 A f n x)) = ((term167 A f n x) = (term51 A f x n)).
Proof. exact (MK_COMB (@lem7052975 A f n x) (@lem7052976 A f x n)). Qed.
Lemma lem7052978 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term167 A f n x) = (term51 A f x n).
Proof. exact (EQ_MP (@lem7052977 A f x n) (@lem7052969 A f n x)). Qed.
Lemma lem7052979 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7052980 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term171 A f n x) = (term172 A f x n).
Proof. exact (MK_COMB (@lem7052979) (@lem7052978 A f x n)). Qed.
Lemma lem7052981 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term55 A s f n) = (term55 A s f n).
Proof. exact (eq_refl (term55 A s f n)). Qed.
Lemma lem7052982 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term152 A x s f n) = (term173 A x s f n).
Proof. exact (MK_COMB (@lem7052980 A f x n) (@lem7052981 A s f n)). Qed.
Lemma lem7052983 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term174 A x s f n.
Proof. exact (fun h0 : ~ False => @lem7052982 A x s f n). Qed.
Lemma lem7052984 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term175 A x s f n.
Proof. exact (@lem7052960 A (term173 A x s f n) f n x s h1). Qed.
Lemma lem7052985 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term150 A x s f n) = (term176 A x s f n).
Proof. exact (@lem7052984 A f n x s h1 (@lem7052983 A x s f n)). Qed.
Lemma lem7052987 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7052988 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7052987 nat t1 t2). Qed.
Lemma lem7052989 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term176 A x s f n) = (term173 A x s f n).
Proof. exact (@lem7052988 (term55 A s f n) (term173 A x s f n)). Qed.
Lemma lem7052990 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term150 A x s f n) = (term173 A x s f n).
Proof. exact (TRANS (@lem7052985 A f n x s h1) (@lem7052989 A x s f n)). Qed.
Lemma lem7052991 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term149 A x s f n) = (term173 A x s f n).
Proof. exact (TRANS (@lem7052933 A f n x s h1) (@lem7052990 A f n x s h1)). Qed.
Lemma lem7052992 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7052993 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term177 A x s f n) = (term178 A x s f n).
Proof. exact (MK_COMB (@lem7052992) (@lem7052991 A f n x s h1)). Qed.
Lemma lem7052994 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7052995 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term84 A x s f n) = (term179 A x s f n).
Proof. exact (MK_COMB (@lem7052993 A f n x s h1) (@lem7052994 n)). Qed.
Lemma lem7052996 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : ((term83 A x s f n) = (term84 A x s f n)) = ((term145 A x s f n) = (term179 A x s f n)).
Proof. exact (MK_COMB (@lem7052924 A f n x s h1) (@lem7052995 A f n x s h1)). Qed.
Lemma lem7052999 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term180 A x s f n.
Proof. exact (fun h0 : term79 A f n x s => @lem7052996 A f n x s h0). Qed.
Lemma lem7053000 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term181 A x s f n.
Proof. exact (@lem7052857 A f n x s ((term145 A x s f n) = (term179 A x s f n))). Qed.
Lemma lem7053001 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term86 A x s f n) = (term182 A x s f n).
Proof. exact (@lem7053000 A x s f n (@lem7052999 A x s f n)). Qed.
Lemma lem7053047 {A : Type'} (x : A) (f : A -> nat) (n : nat) : (term88 A x f n) = (term183 A x f n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7053001 A x s f n)). Qed.
Lemma lem7053093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7053094 {A : Type'} (x : A) (f : A -> nat) (n : nat) : (term90 A x f n) = (term184 A x f n).
Proof. exact (MK_COMB (@lem7053093 A) (@lem7053047 A x f n)). Qed.
Lemma lem7053144 {A : Type'} (f : A -> nat) (n : nat) : (term92 A f n) = (term185 A f n).
Proof. exact (fun_ext (fun x : A => @lem7053094 A x f n)). Qed.
Lemma lem7053194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7053195 {A : Type'} (f : A -> nat) (n : nat) : (term94 A f n) = (term186 A f n).
Proof. exact (MK_COMB (@lem7053194 A) (@lem7053144 A f n)). Qed.
Lemma lem7053249 {A : Type'} (f : A -> nat) (n : nat) : (term96 A f n) = (term187 A f n).
Proof. exact (MK_COMB (@lem7052827 A f n) (@lem7053195 A f n)). Qed.
Lemma lem7053251 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7053252 {A : Type'} (f : A -> nat) (n : nat) : (term187 A f n) = (term186 A f n).
Proof. exact (@lem7053251 (term186 A f n)). Qed.
Lemma lem7053306 {A : Type'} (f : A -> nat) (n : nat) : (term96 A f n) = (term186 A f n).
Proof. exact (TRANS (@lem7053249 A f n) (@lem7053252 A f n)). Qed.
Lemma lem7053307 {A : Type'} (f : A -> nat) (n : nat) : (term186 A f n) = (term96 A f n).
Proof. exact (SYM (@lem7053306 A f n)). Qed.
Lemma lem7053308 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : term79 A f n x s.
Proof. exact (h1). Qed.
Lemma lem7053310 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term46 A s f n) = (term57 A s f n).
Proof. exact (h1). Qed.
Lemma lem7053314 (a : nat) (b : nat) (n : nat) : (term5 a b n) = (term4 a b n).
Proof. exact (EQ_MP (@lem7052624 a b n) (@lem7052623 a b n)). Qed.
Lemma lem7053315 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term145 A x s f n) = (term188 A x s f n).
Proof. exact (@lem7053314 (f x) (@nsum A s f) n). Qed.
Lemma lem7053316 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7053317 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term147 A x s f n) = (term189 A x s f n).
Proof. exact (MK_COMB (@lem7053316) (@lem7053315 A x s f n)). Qed.
Lemma lem7053318 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term179 A x s f n) = (term179 A x s f n).
Proof. exact (eq_refl (term179 A x s f n)). Qed.
Lemma lem7053319 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term145 A x s f n) = (term179 A x s f n)) = ((term188 A x s f n) = (term179 A x s f n)).
Proof. exact (MK_COMB (@lem7053317 A x s f n) (@lem7053318 A x s f n)). Qed.
Lemma lem7053320 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term188 A x s f n) = (term179 A x s f n)) = ((term145 A x s f n) = (term179 A x s f n)).
Proof. exact (SYM (@lem7053319 A x s f n)). Qed.
Lemma lem7053341 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term46 A s f n) = (term57 A s f n).
Proof. exact (h1). Qed.
Lemma lem7053342 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term172 A f x n) = (term172 A f x n).
Proof. exact (eq_refl (term172 A f x n)). Qed.
Lemma lem7053343 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term190 A x s f n) = (term191 A x s f n).
Proof. exact (MK_COMB (@lem7053342 A f x n) (@lem7053341 A s f n h1)). Qed.
Lemma lem7053344 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053345 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term192 A x s f n) = (term193 A x s f n).
Proof. exact (MK_COMB (@lem7053344) (@lem7053343 A x s f n h1)). Qed.
Lemma lem7053346 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053347 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term188 A x s f n) = (term194 A x s f n).
Proof. exact (MK_COMB (@lem7053345 A x s f n h1) (@lem7053346 n)). Qed.
Lemma lem7053348 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7053349 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term189 A x s f n) = (term195 A x s f n).
Proof. exact (MK_COMB (@lem7053348) (@lem7053347 A x s f n h1)). Qed.
Lemma lem7053350 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term179 A x s f n) = (term179 A x s f n).
Proof. exact (eq_refl (term179 A x s f n)). Qed.
Lemma lem7053351 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : ((term188 A x s f n) = (term179 A x s f n)) = ((term194 A x s f n) = (term179 A x s f n)).
Proof. exact (MK_COMB (@lem7053349 A x s f n h1) (@lem7053350 A x s f n)). Qed.
Lemma lem7053354 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : ((term194 A x s f n) = (term179 A x s f n)) = ((term188 A x s f n) = (term179 A x s f n)).
Proof. exact (SYM (@lem7053351 A x s f n h1)). Qed.
Lemma lem7053358 (a : nat) (b : nat) (n : nat) : (term5 a b n) = (term4 a b n).
Proof. exact (EQ_MP (@lem7052597 a b n) (@lem7052596 a b n)). Qed.
Lemma lem7053359 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term194 A x s f n) = (term196 A x s f n).
Proof. exact (@lem7053358 (term51 A f x n) (term57 A s f n) n). Qed.
Lemma lem7053360 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7053361 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term195 A x s f n) = (term197 A x s f n).
Proof. exact (MK_COMB (@lem7053360) (@lem7053359 A x s f n)). Qed.
Lemma lem7053363 (a : nat) (b : nat) (n : nat) : (term5 a b n) = (term4 a b n).
Proof. exact (EQ_MP (@lem7052597 a b n) (@lem7052596 a b n)). Qed.
Lemma lem7053364 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term179 A x s f n) = (term198 A x s f n).
Proof. exact (@lem7053363 (term51 A f x n) (term55 A s f n) n). Qed.
Lemma lem7053365 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term194 A x s f n) = (term179 A x s f n)) = ((term196 A x s f n) = (term198 A x s f n)).
Proof. exact (MK_COMB (@lem7053361 A x s f n) (@lem7053364 A x s f n)). Qed.
Lemma lem7053366 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term196 A x s f n) = (term198 A x s f n)) = ((term194 A x s f n) = (term179 A x s f n)).
Proof. exact (SYM (@lem7053365 A x s f n)). Qed.
Lemma lem7053370 (m : nat) (n : nat) : (term3 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem7052570 m n) (@lem7052569 m n)). Qed.
Lemma lem7053371 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term199 A f x n) = (term51 A f x n).
Proof. exact (@lem7053370 (f x) n). Qed.
Lemma lem7053372 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7053373 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term200 A f x n) = (term172 A f x n).
Proof. exact (MK_COMB (@lem7053372) (@lem7053371 A f x n)). Qed.
Lemma lem7053375 (m : nat) (n : nat) : (term3 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem7052570 m n) (@lem7052569 m n)). Qed.
Lemma lem7053376 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term201 A s f n) = (term57 A s f n).
Proof. exact (@lem7053375 (term55 A s f n) n). Qed.
Lemma lem7053377 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term202 A x s f n) = (term191 A x s f n).
Proof. exact (MK_COMB (@lem7053373 A f x n) (@lem7053376 A s f n)). Qed.
Lemma lem7053378 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053379 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term203 A x s f n) = (term193 A x s f n).
Proof. exact (MK_COMB (@lem7053378) (@lem7053377 A x s f n)). Qed.
Lemma lem7053380 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053381 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term196 A x s f n) = (term194 A x s f n).
Proof. exact (MK_COMB (@lem7053379 A x s f n) (@lem7053380 n)). Qed.
Lemma lem7053382 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7053383 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term197 A x s f n) = (term195 A x s f n).
Proof. exact (MK_COMB (@lem7053382) (@lem7053381 A x s f n)). Qed.
Lemma lem7053385 (m : nat) (n : nat) : (term3 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem7052570 m n) (@lem7052569 m n)). Qed.
Lemma lem7053386 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term199 A f x n) = (term51 A f x n).
Proof. exact (@lem7053385 (f x) n). Qed.
Lemma lem7053387 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7053388 {A : Type'} (f : A -> nat) (x : A) (n : nat) : (term200 A f x n) = (term172 A f x n).
Proof. exact (MK_COMB (@lem7053387) (@lem7053386 A f x n)). Qed.
Lemma lem7053389 {A : Type'} (s : A -> Prop) (f : A -> nat) (n : nat) : (term57 A s f n) = (term57 A s f n).
Proof. exact (eq_refl (term57 A s f n)). Qed.
Lemma lem7053390 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term204 A x s f n) = (term191 A x s f n).
Proof. exact (MK_COMB (@lem7053388 A f x n) (@lem7053389 A s f n)). Qed.
Lemma lem7053391 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem7053392 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term205 A x s f n) = (term193 A x s f n).
Proof. exact (MK_COMB (@lem7053391) (@lem7053390 A x s f n)). Qed.
Lemma lem7053393 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7053394 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term198 A x s f n) = (term194 A x s f n).
Proof. exact (MK_COMB (@lem7053392 A x s f n) (@lem7053393 n)). Qed.
Lemma lem7053395 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term196 A x s f n) = (term198 A x s f n)) = ((term194 A x s f n) = (term194 A x s f n)).
Proof. exact (MK_COMB (@lem7053383 A x s f n) (@lem7053394 A x s f n)). Qed.
Lemma lem7053397 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7053398 (x : nat) : (x = x) = True.
Proof. exact (@lem7053397 nat x). Qed.
Lemma lem7053399 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term194 A x s f n) = (term194 A x s f n)) = True.
Proof. exact (@lem7053398 (term194 A x s f n)). Qed.
Lemma lem7053400 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : ((term196 A x s f n) = (term198 A x s f n)) = True.
Proof. exact (TRANS (@lem7053395 A x s f n) (@lem7053399 A x s f n)). Qed.
Lemma lem7053401 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : True = ((term196 A x s f n) = (term198 A x s f n)).
Proof. exact (SYM (@lem7053400 A x s f n)). Qed.
Lemma lem7053402 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term196 A x s f n) = (term198 A x s f n).
Proof. exact (EQ_MP (@lem7053401 A x s f n) (@lem0)). Qed.
Lemma lem7053403 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : (term194 A x s f n) = (term179 A x s f n).
Proof. exact (EQ_MP (@lem7053366 A x s f n) (@lem7053402 A x s f n)). Qed.
Lemma lem7053404 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term188 A x s f n) = (term179 A x s f n).
Proof. exact (EQ_MP (@lem7053354 A x s f n h1) (@lem7053403 A x s f n)). Qed.
Lemma lem7053405 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term145 A x s f n) = (term179 A x s f n).
Proof. exact (EQ_MP (@lem7053320 A x s f n) (@lem7053404 A x s f n h1)). Qed.
Lemma lem7053407 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term46 A s f n) = (term57 A s f n).
Proof. exact (proj1 (@lem7053308 A f n x s h1)). Qed.
Lemma lem7053410 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : ((term46 A s f n) = (term57 A s f n)) = ((term145 A x s f n) = (term179 A x s f n)).
Proof. exact (prop_ext (fun h2 : (term46 A s f n) = (term57 A s f n) => @lem7053405 A x s f n h1) (fun h2 : (term145 A x s f n) = (term179 A x s f n) => @lem7053310 A s f n h1)). Qed.
Lemma lem7053411 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) (h1 : (term46 A s f n) = (term57 A s f n)) : (term145 A x s f n) = (term179 A x s f n).
Proof. exact (EQ_MP (@lem7053410 A x s f n h1) (@lem7053310 A s f n h1)). Qed.
Lemma lem7053412 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : ((term46 A s f n) = (term57 A s f n)) = ((term145 A x s f n) = (term179 A x s f n)).
Proof. exact (prop_ext (fun h2 : (term46 A s f n) = (term57 A s f n) => @lem7053411 A x s f n h2) (fun h2 : (term145 A x s f n) = (term179 A x s f n) => @lem7053407 A f n x s h1)). Qed.
Lemma lem7053413 {A : Type'} (f : A -> nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term79 A f n x s) : (term145 A x s f n) = (term179 A x s f n).
Proof. exact (EQ_MP (@lem7053412 A f n x s h1) (@lem7053407 A f n x s h1)). Qed.
Lemma lem7053414 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (n : nat) : term182 A x s f n.
Proof. exact (fun h0 : term79 A f n x s => @lem7053413 A f n x s h0). Qed.
Lemma lem7053419 {A : Type'} (x : A) (f : A -> nat) (n : nat) : term184 A x f n.
Proof. exact (fun s : A -> Prop => @lem7053414 A x s f n). Qed.
Lemma lem7053424 {A : Type'} (f : A -> nat) (n : nat) : term186 A f n.
Proof. exact (fun x : A => @lem7053419 A x f n). Qed.
Lemma lem7053425 {A : Type'} (f : A -> nat) (n : nat) : term96 A f n.
Proof. exact (EQ_MP (@lem7053307 A f n) (@lem7053424 A f n)). Qed.
Lemma lem7053427 {A : Type'} (f : A -> nat) (n : nat) : term63 A f n.
Proof. exact (@lem7052798 A f n (@lem7053425 A f n)). Qed.
Lemma lem7053428 {A : Type'} (f : A -> nat) (n : nat) : term63 A f n.
Proof. exact (or_elim (@lem7052665 n) (fun h0 : n = (NUMERAL 0) => @lem7052736 A f n h0) (fun h0 : term206 n => @lem7053427 A f n)). Qed.
Lemma lem7053433 {A : Type'} (f : A -> nat) : term207 A f.
Proof. exact (fun n : nat => @lem7053428 A f n). Qed.
Lemma lem7053438 {A : Type'} : term208 A.
Proof. exact (fun f : A -> nat => @lem7053433 A f). Qed.
