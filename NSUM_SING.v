Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SING_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import FINITE_RULES_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6960523 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem6960539 : term1.
Proof. exact (proj1 (@lem6960523)). Qed.
Lemma lem6960540 (m : nat) : term2 m.
Proof. exact (@lem6960539 m). Qed.
Lemma lem6960541 (m : nat) : (term2 m) = ((term3 m) = m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem6960547 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem6960548 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem6960549 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem6960548 A x) (@lem6960547 A x)). Qed.
Lemma lem6960550 {A : Type'} (x : A) : term6 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem6960568 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem6960569 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem6960571 {_126525 : Type'} : term7 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6960572 {_126525 : Type'} (x : _126525) : term8 _126525 x.
Proof. exact (@lem6960571 _126525 x). Qed.
Lemma lem6960573 {_126525 : Type'} (x : _126525) : (term8 _126525 x) = (term9 _126525 x).
Proof. exact (eq_refl (term8 _126525 x)). Qed.
Lemma lem6960574 {_126525 : Type'} (x : _126525) : term9 _126525 x.
Proof. exact (EQ_MP (@lem6960573 _126525 x) (@lem6960572 _126525 x)). Qed.
Lemma lem6960575 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term10 _126525 x f.
Proof. exact (@lem6960574 _126525 x f). Qed.
Lemma lem6960576 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term10 _126525 x f) = (term11 _126525 x f).
Proof. exact (eq_refl (term10 _126525 x f)). Qed.
Lemma lem6960577 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term11 _126525 x f.
Proof. exact (EQ_MP (@lem6960576 _126525 x f) (@lem6960575 _126525 x f)). Qed.
Lemma lem6960578 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term12 _126525 x f s.
Proof. exact (@lem6960577 _126525 x f s). Qed.
Lemma lem6960579 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term12 _126525 x f s) = (term13 _126525 x s f).
Proof. exact (eq_refl (term12 _126525 x f s)). Qed.
Lemma lem6960580 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term13 _126525 x s f.
Proof. exact (EQ_MP (@lem6960579 _126525 x s f) (@lem6960578 _126525 x f s)). Qed.
Lemma lem6960581 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6960582 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term14 _126525 x s f) = (term15 _126525 x s f).
Proof. exact (@lem6960580 _126525 x s f (@lem6960581 _126525 s h1)). Qed.
Lemma lem6960588 {_126486 : Type'} : term16 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6960589 {_126486 : Type'} (f : _126486 -> nat) : term17 _126486 f.
Proof. exact (@lem6960588 _126486 f). Qed.
Lemma lem6960590 {_126486 : Type'} (f : _126486 -> nat) : (term17 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term17 _126486 f)). Qed.
Lemma lem6960603 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term13 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6960582 _126525 x f s h0). Qed.
Lemma lem6960604 {_127448 : Type'} (x : _127448) (s : _127448 -> Prop) (f : _127448 -> nat) : term13 _127448 x s f.
Proof. exact (@lem6960603 _127448 x s f). Qed.
Lemma lem6960605 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : term18 _127448 x f.
Proof. exact (@lem6960604 _127448 x (@EMPTY _127448) f). Qed.
Lemma lem6960607 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem6960569 A) (@lem6960568 A)). Qed.
Lemma lem6960608 {_127448 : Type'} : (@FINITE _127448 (@EMPTY _127448)) = True.
Proof. exact (@lem6960607 _127448). Qed.
Lemma lem6960609 {_127448 : Type'} : True = (@FINITE _127448 (@EMPTY _127448)).
Proof. exact (SYM (@lem6960608 _127448)). Qed.
Lemma lem6960610 {_127448 : Type'} : @FINITE _127448 (@EMPTY _127448).
Proof. exact (EQ_MP (@lem6960609 _127448) (@lem0)). Qed.
Lemma lem6960611 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : (term19 _127448 x f) = (term20 _127448 x f).
Proof. exact (@lem6960605 _127448 x f (@lem6960610 _127448)). Qed.
Lemma lem6960613 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term21 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6960614 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term22 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6960613 _2963 g t e g' t' e'). Qed.
Lemma lem6960615 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term23 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6960614 _2963 g t e g' t'). Qed.
Lemma lem6960616 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term24 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6960615 _2963 g t e g'). Qed.
Lemma lem6960617 (g : Prop) (t : nat) (e : nat) : term25 g t e.
Proof. exact (@lem6960616 nat g t e). Qed.
Lemma lem6960618 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : term26 _127448 x f.
Proof. exact (@lem6960617 (@IN _127448 x (@EMPTY _127448)) (@nsum _127448 (@EMPTY _127448) f) (term27 _127448 x f)). Qed.
Lemma lem6960619 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) : term28 _127448 x f g'.
Proof. exact (@lem6960618 _127448 x f g'). Qed.
Lemma lem6960620 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) : (term28 _127448 x f g') = (term29 _127448 x f g').
Proof. exact (eq_refl (term28 _127448 x f g')). Qed.
Lemma lem6960621 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) : term29 _127448 x f g'.
Proof. exact (EQ_MP (@lem6960620 _127448 x f g') (@lem6960619 _127448 x f g')). Qed.
Lemma lem6960622 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) : term30 _127448 x f g' t'.
Proof. exact (@lem6960621 _127448 x f g' t'). Qed.
Lemma lem6960623 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) : (term30 _127448 x f g' t') = (term31 _127448 x f g' t').
Proof. exact (eq_refl (term30 _127448 x f g' t')). Qed.
Lemma lem6960624 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) : term31 _127448 x f g' t'.
Proof. exact (EQ_MP (@lem6960623 _127448 x f g' t') (@lem6960622 _127448 x f g' t')). Qed.
Lemma lem6960625 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term32 _127448 x f g' t' e'.
Proof. exact (@lem6960624 _127448 x f g' t' e'). Qed.
Lemma lem6960626 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term32 _127448 x f g' t' e') = (term33 _127448 x f g' t' e').
Proof. exact (eq_refl (term32 _127448 x f g' t' e')). Qed.
Lemma lem6960627 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (g' : Prop) (t' : nat) (e' : nat) : term33 _127448 x f g' t' e'.
Proof. exact (EQ_MP (@lem6960626 _127448 x f g' t' e') (@lem6960625 _127448 x f g' t' e')). Qed.
Lemma lem6960629 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6960550 A x (@lem6960549 A x)). Qed.
Lemma lem6960630 {_127448 : Type'} (x : _127448) : (@IN _127448 x (@EMPTY _127448)) = False.
Proof. exact (@lem6960629 _127448 x). Qed.
Lemma lem6960631 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (t' : nat) (e' : nat) : term34 _127448 x f t' e'.
Proof. exact (@lem6960627 _127448 x f False t' e'). Qed.
Lemma lem6960632 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (t' : nat) (e' : nat) : term35 _127448 x f t' e'.
Proof. exact (@lem6960631 _127448 x f t' e' (@lem6960630 _127448 x)). Qed.
Lemma lem6960637 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6960590 _126486 f) (@lem6960589 _126486 f)). Qed.
Lemma lem6960638 {_127448 : Type'} (f : _127448 -> nat) : (@nsum _127448 (@EMPTY _127448) f) = (NUMERAL 0).
Proof. exact (@lem6960637 _127448 f). Qed.
Lemma lem6960639 {_127448 : Type'} (f : _127448 -> nat) : term36 _127448 f.
Proof. exact (fun h0 : False => @lem6960638 _127448 f). Qed.
Lemma lem6960640 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (e' : nat) : term37 _127448 x f e'.
Proof. exact (@lem6960632 _127448 x f (NUMERAL 0) e'). Qed.
Lemma lem6960641 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (e' : nat) : term38 _127448 x f e'.
Proof. exact (@lem6960640 _127448 x f e' (@lem6960639 _127448 f)). Qed.
Lemma lem6960648 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6960590 _126486 f) (@lem6960589 _126486 f)). Qed.
Lemma lem6960649 {_127448 : Type'} (f : _127448 -> nat) : (@nsum _127448 (@EMPTY _127448) f) = (NUMERAL 0).
Proof. exact (@lem6960648 _127448 f). Qed.
Lemma lem6960650 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term39 _127448 f x) = (term39 _127448 f x).
Proof. exact (eq_refl (term39 _127448 f x)). Qed.
Lemma lem6960651 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term27 _127448 x f) = (term40 _127448 f x).
Proof. exact (MK_COMB (@lem6960650 _127448 f x) (@lem6960649 _127448 f)). Qed.
Lemma lem6960653 (m : nat) : (term3 m) = m.
Proof. exact (EQ_MP (@lem6960541 m) (@lem6960540 m)). Qed.
Lemma lem6960654 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term40 _127448 f x) = (f x).
Proof. exact (@lem6960653 (f x)). Qed.
Lemma lem6960655 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term27 _127448 x f) = (f x).
Proof. exact (TRANS (@lem6960651 _127448 f x) (@lem6960654 _127448 f x)). Qed.
Lemma lem6960656 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : term41 _127448 f x.
Proof. exact (fun h0 : ~ False => @lem6960655 _127448 f x). Qed.
Lemma lem6960657 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : term42 _127448 f x.
Proof. exact (@lem6960641 _127448 x f (f x)). Qed.
Lemma lem6960658 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term20 _127448 x f) = (term43 _127448 f x).
Proof. exact (@lem6960657 _127448 f x (@lem6960656 _127448 f x)). Qed.
Lemma lem6960660 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6960661 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6960660 nat t1 t2). Qed.
Lemma lem6960662 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term43 _127448 f x) = (f x).
Proof. exact (@lem6960661 (NUMERAL 0) (f x)). Qed.
Lemma lem6960663 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term20 _127448 x f) = (f x).
Proof. exact (TRANS (@lem6960658 _127448 f x) (@lem6960662 _127448 f x)). Qed.
Lemma lem6960664 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term19 _127448 x f) = (f x).
Proof. exact (TRANS (@lem6960611 _127448 x f) (@lem6960663 _127448 f x)). Qed.
Lemma lem6960665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6960666 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term44 _127448 x f) = (term45 _127448 f x).
Proof. exact (MK_COMB (@lem6960665) (@lem6960664 _127448 f x)). Qed.
Lemma lem6960667 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6960668 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : ((term19 _127448 x f) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem6960666 _127448 f x) (@lem6960667 _127448 f x)). Qed.
Lemma lem6960670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6960671 (x : nat) : (x = x) = True.
Proof. exact (@lem6960670 nat x). Qed.
Lemma lem6960672 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : ((f x) = (f x)) = True.
Proof. exact (@lem6960671 (f x)). Qed.
Lemma lem6960673 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : ((term19 _127448 x f) = (f x)) = True.
Proof. exact (TRANS (@lem6960668 _127448 f x) (@lem6960672 _127448 f x)). Qed.
Lemma lem6960674 {_127448 : Type'} (f : _127448 -> nat) : (term46 _127448 f) = (term47 _127448).
Proof. exact (fun_ext (fun x : _127448 => @lem6960673 _127448 f x)). Qed.
Lemma lem6960675 {_127448 : Type'} : (@all _127448) = (@all _127448).
Proof. exact (eq_refl (@all _127448)). Qed.
Lemma lem6960676 {_127448 : Type'} (f : _127448 -> nat) : (term48 _127448 f) = (term49 _127448).
Proof. exact (MK_COMB (@lem6960675 _127448) (@lem6960674 _127448 f)). Qed.
Lemma lem6960678 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960679 {_127448 : Type'} (t : Prop) : (term50 _127448 t) = t.
Proof. exact (@lem6960678 _127448 t). Qed.
Lemma lem6960680 {_127448 : Type'} : (term49 _127448) = True.
Proof. exact (@lem6960679 _127448 True). Qed.
Lemma lem6960681 {_127448 : Type'} (f : _127448 -> nat) : (term48 _127448 f) = True.
Proof. exact (TRANS (@lem6960676 _127448 f) (@lem6960680 _127448)). Qed.
Lemma lem6960682 {_127448 : Type'} : (term51 _127448) = (term52 _127448).
Proof. exact (fun_ext (fun f : _127448 -> nat => @lem6960681 _127448 f)). Qed.
Lemma lem6960683 {_127448 : Type'} : (@all (_127448 -> nat)) = (@all (_127448 -> nat)).
Proof. exact (eq_refl (@all (_127448 -> nat))). Qed.
Lemma lem6960684 {_127448 : Type'} : (term53 _127448) = (term54 _127448).
Proof. exact (MK_COMB (@lem6960683 _127448) (@lem6960682 _127448)). Qed.
Lemma lem6960686 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960687 {_127448 : Type'} (t : Prop) : (term55 _127448 t) = t.
Proof. exact (@lem6960686 (_127448 -> nat) t). Qed.
Lemma lem6960688 {_127448 : Type'} : (term54 _127448) = True.
Proof. exact (@lem6960687 _127448 True). Qed.
Lemma lem6960689 {_127448 : Type'} : (term53 _127448) = True.
Proof. exact (TRANS (@lem6960684 _127448) (@lem6960688 _127448)). Qed.
Lemma lem6960690 {_127448 : Type'} : True = (term53 _127448).
Proof. exact (SYM (@lem6960689 _127448)). Qed.
Lemma lem6960691 {_127448 : Type'} : term53 _127448.
Proof. exact (EQ_MP (@lem6960690 _127448) (@lem0)). Qed.
