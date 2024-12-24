Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_SING_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_RULES_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm21385_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5804551 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5804552 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5804553 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5804552 A x) (@lem5804551 A x)). Qed.
Lemma lem5804554 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5804572 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem5804573 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem5804575 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5804576 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term3 _120477 _120519 _120521 op) = (term4 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term3 _120477 _120519 _120521 op)). Qed.
Lemma lem5804577 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term4 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5804576 _120477 _120519 _120521 op) (@lem5804575 _120477 _120519 _120521 op)). Qed.
Lemma lem5804578 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5804579 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term5 _120477 _120519 _120521 op.
Proof. exact (@lem5804577 _120477 _120519 _120521 op (@lem5804578 _120519 op h1)). Qed.
Lemma lem5804580 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term6 _120519 _120521 op.
Proof. exact (proj2 (@lem5804579 Prop _120519 _120521 op h1)). Qed.
Lemma lem5804581 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term7 _120519 _120521 op f.
Proof. exact (@lem5804580 _120519 _120521 op h1 f). Qed.
Lemma lem5804582 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term7 _120519 _120521 op f) = (term8 _120519 _120521 op f).
Proof. exact (eq_refl (term7 _120519 _120521 op f)). Qed.
Lemma lem5804583 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term8 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5804582 _120519 _120521 op f) (@lem5804581 _120519 _120521 f op h1)). Qed.
Lemma lem5804584 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term9 _120519 _120521 op f x.
Proof. exact (@lem5804583 _120519 _120521 f op h1 x). Qed.
Lemma lem5804585 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term9 _120519 _120521 op f x) = (term10 _120519 _120521 x op f).
Proof. exact (eq_refl (term9 _120519 _120521 op f x)). Qed.
Lemma lem5804586 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term10 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5804585 _120519 _120521 x op f) (@lem5804584 _120519 _120521 f x op h1)). Qed.
Lemma lem5804587 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term11 _120519 _120521 x op f s.
Proof. exact (@lem5804586 _120519 _120521 x f op h1 s). Qed.
Lemma lem5804588 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term11 _120519 _120521 x op f s) = (term12 _120519 _120521 x op s f).
Proof. exact (eq_refl (term11 _120519 _120521 x op f s)). Qed.
Lemma lem5804589 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term12 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5804588 _120519 _120521 x op s f) (@lem5804587 _120519 _120521 x f s op h1)). Qed.
Lemma lem5804590 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5804591 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term13 _120519 _120521 op x s f) = (term14 _120519 _120521 x op s f).
Proof. exact (@lem5804589 _120519 _120521 x s f op h2 (@lem5804590 _120521 s h1)). Qed.
Lemma lem5804592 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term15 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5804591 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5804593 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term16 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5804592 _120519 _120521 x op f s h0). Qed.
Lemma lem5804595 (p : Prop) (q : Prop) (r : Prop) : (term17 p q r) = (term18 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5804600 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term16 _120519 _120521 x op s f) = (term19 _120519 _120521 x op s f).
Proof. exact (@lem5804595 (@FINITE _120521 s) (@monoidal _120519 op) ((term13 _120519 _120521 op x s f) = (term14 _120519 _120521 x op s f))). Qed.
Lemma lem5804602 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term20 _120477 _120519 op.
Proof. exact (proj1 (@lem5804579 _120477 _120519 Prop op h1)). Qed.
Lemma lem5804603 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term21 _120477 _120519 op f.
Proof. exact (@lem5804602 _120477 _120519 op h1 f). Qed.
Lemma lem5804604 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term21 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term21 _120477 _120519 op f)). Qed.
Lemma lem5804605 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5804604 _120477 _120519 f op) (@lem5804603 _120477 _120519 f op h1)). Qed.
Lemma lem5804618 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term22 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5804619 (p : Prop) (q : Prop) (p' : Prop) : term23 p q p'.
Proof. exact (fun q' : Prop => @lem5804618 p q p' q'). Qed.
Lemma lem5804620 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (fun p' : Prop => @lem5804619 p q p'). Qed.
Lemma lem5804621 {A B : Type'} (op : type1400 B) : term25 A B op.
Proof. exact (@lem5804620 (@monoidal B op) (term26 A B op)). Qed.
Lemma lem5804622 {A B : Type'} (op : type1400 B) (p' : Prop) : term27 A B op p'.
Proof. exact (@lem5804621 A B op p'). Qed.
Lemma lem5804623 {A B : Type'} (op : type1400 B) (p' : Prop) : (term27 A B op p') = (term28 A B op p').
Proof. exact (eq_refl (term27 A B op p')). Qed.
Lemma lem5804624 {A B : Type'} (op : type1400 B) (p' : Prop) : term28 A B op p'.
Proof. exact (EQ_MP (@lem5804623 A B op p') (@lem5804622 A B op p')). Qed.
Lemma lem5804625 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term29 A B op p' q'.
Proof. exact (@lem5804624 A B op p' q'). Qed.
Lemma lem5804626 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : (term29 A B op p' q') = (term30 A B op p' q').
Proof. exact (eq_refl (term29 A B op p' q')). Qed.
Lemma lem5804627 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term30 A B op p' q'.
Proof. exact (EQ_MP (@lem5804626 A B op p' q') (@lem5804625 A B op p' q')). Qed.
Lemma lem5804628 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5804629 {A B : Type'} (op : type1400 B) (q' : Prop) : term31 A B op q'.
Proof. exact (@lem5804627 A B op (@monoidal B op) q'). Qed.
Lemma lem5804630 {A B : Type'} (op : type1400 B) (q' : Prop) : term32 A B op q'.
Proof. exact (@lem5804629 A B op q' (@lem5804628 B op)). Qed.
Lemma lem5804631 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5804632 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5804645 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term19 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5804600 _120519 _120521 x op s f) (@lem5804593 _120519 _120521 x op s f)). Qed.
Lemma lem5804646 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term33 A B x op s f.
Proof. exact (@lem5804645 B A x op s f). Qed.
Lemma lem5804647 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : term34 A B x op f.
Proof. exact (@lem5804646 A B x op (@EMPTY A) f). Qed.
Lemma lem5804651 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5804573 A) (@lem5804572 A)). Qed.
Lemma lem5804652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5804653 {A : Type'} : (term35 A) = (and True).
Proof. exact (MK_COMB (@lem5804652) (@lem5804651 A)). Qed.
Lemma lem5804655 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5804632 B op) (@lem5804631 B op h1)). Qed.
Lemma lem5804656 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term36 A B op) = (True /\ True).
Proof. exact (MK_COMB (@lem5804653 A) (@lem5804655 B op h1)). Qed.
Lemma lem5804658 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5804659 : (True /\ True) = True.
Proof. exact (@lem5804658 True). Qed.
Lemma lem5804660 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term36 A B op) = True.
Proof. exact (TRANS (@lem5804656 A B op h1) (@lem5804659)). Qed.
Lemma lem5804661 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (term36 A B op).
Proof. exact (SYM (@lem5804660 A B op h1)). Qed.
Lemma lem5804662 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term36 A B op.
Proof. exact (EQ_MP (@lem5804661 A B op h1) (@lem0)). Qed.
Lemma lem5804663 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term37 A B op x f) = (term38 A B x op f).
Proof. exact (@lem5804647 A B x op f (@lem5804662 A B op h1)). Qed.
Lemma lem5804665 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term39 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5804666 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term40 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5804665 _2963 g t e g' t' e'). Qed.
Lemma lem5804667 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term41 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5804666 _2963 g t e g' t'). Qed.
Lemma lem5804668 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term42 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5804667 _2963 g t e g'). Qed.
Lemma lem5804669 {B : Type'} (g : Prop) (t : B) (e : B) : term42 B g t e.
Proof. exact (@lem5804668 B g t e). Qed.
Lemma lem5804670 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : term43 A B x op f.
Proof. exact (@lem5804669 B (@IN A x (@EMPTY A)) (@iterate B A op (@EMPTY A) f) (term44 A B x op f)). Qed.
Lemma lem5804671 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) : term45 A B x op f g'.
Proof. exact (@lem5804670 A B x op f g'). Qed.
Lemma lem5804672 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) : (term45 A B x op f g') = (term46 A B x op f g').
Proof. exact (eq_refl (term45 A B x op f g')). Qed.
Lemma lem5804673 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) : term46 A B x op f g'.
Proof. exact (EQ_MP (@lem5804672 A B x op f g') (@lem5804671 A B x op f g')). Qed.
Lemma lem5804674 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) : term47 A B x op f g' t'.
Proof. exact (@lem5804673 A B x op f g' t'). Qed.
Lemma lem5804675 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) : (term47 A B x op f g' t') = (term48 A B x op f g' t').
Proof. exact (eq_refl (term47 A B x op f g' t')). Qed.
Lemma lem5804676 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) : term48 A B x op f g' t'.
Proof. exact (EQ_MP (@lem5804675 A B x op f g' t') (@lem5804674 A B x op f g' t')). Qed.
Lemma lem5804677 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term49 A B x op f g' t' e'.
Proof. exact (@lem5804676 A B x op f g' t' e'). Qed.
Lemma lem5804678 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term49 A B x op f g' t' e') = (term50 A B x op f g' t' e').
Proof. exact (eq_refl (term49 A B x op f g' t' e')). Qed.
Lemma lem5804679 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term50 A B x op f g' t' e'.
Proof. exact (EQ_MP (@lem5804678 A B x op f g' t' e') (@lem5804677 A B x op f g' t' e')). Qed.
Lemma lem5804681 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5804554 A x (@lem5804553 A x)). Qed.
Lemma lem5804682 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5804681 A x). Qed.
Lemma lem5804683 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (t' : B) (e' : B) : term51 A B x op f t' e'.
Proof. exact (@lem5804679 A B x op f False t' e'). Qed.
Lemma lem5804684 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (t' : B) (e' : B) : term52 A B x op f t' e'.
Proof. exact (@lem5804683 A B x op f t' e' (@lem5804682 A x)). Qed.
Lemma lem5804689 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term53 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5804605 _120477 _120519 f op h0). Qed.
Lemma lem5804690 {A B : Type'} (f : A -> B) (op : type1400 B) : term53 A B f op.
Proof. exact (@lem5804689 A B f op). Qed.
Lemma lem5804692 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5804632 B op) (@lem5804631 B op h1)). Qed.
Lemma lem5804693 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5804692 B op h1)). Qed.
Lemma lem5804694 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5804693 B op h1) (@lem0)). Qed.
Lemma lem5804695 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (@lem5804690 A B f op (@lem5804694 B op h1)). Qed.
Lemma lem5804696 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term54 A B f op.
Proof. exact (fun h0 : False => @lem5804695 A B f op h1). Qed.
Lemma lem5804697 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (e' : B) : term55 A B x f op e'.
Proof. exact (@lem5804684 A B x op f (@neutral B op) e'). Qed.
Lemma lem5804698 {A B : Type'} (x : A) (f : A -> B) (e' : B) (op : type1400 B) (h1 : @monoidal B op) : term56 A B x f op e'.
Proof. exact (@lem5804697 A B x f op e' (@lem5804696 A B f op h1)). Qed.
Lemma lem5804705 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term53 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5804605 _120477 _120519 f op h0). Qed.
Lemma lem5804706 {A B : Type'} (f : A -> B) (op : type1400 B) : term53 A B f op.
Proof. exact (@lem5804705 A B f op). Qed.
Lemma lem5804708 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5804632 B op) (@lem5804631 B op h1)). Qed.
Lemma lem5804709 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5804708 B op h1)). Qed.
Lemma lem5804710 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5804709 B op h1) (@lem0)). Qed.
Lemma lem5804711 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (@lem5804706 A B f op (@lem5804710 B op h1)). Qed.
Lemma lem5804712 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term57 A B op f x) = (term57 A B op f x).
Proof. exact (eq_refl (term57 A B op f x)). Qed.
Lemma lem5804713 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term44 A B x op f) = (term58 A B f x op).
Proof. exact (MK_COMB (@lem5804712 A B op f x) (@lem5804711 A B f op h1)). Qed.
Lemma lem5804714 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term59 A B f x op.
Proof. exact (fun h0 : ~ False => @lem5804713 A B f x op h1). Qed.
Lemma lem5804715 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term60 A B f x op.
Proof. exact (@lem5804698 A B x f (term58 A B f x op) op h1). Qed.
Lemma lem5804716 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term38 A B x op f) = (term61 A B f x op).
Proof. exact (@lem5804715 A B f x op h1 (@lem5804714 A B f x op h1)). Qed.
Lemma lem5804718 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5804719 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5804718 B t1 t2). Qed.
Lemma lem5804720 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term61 A B f x op) = (term58 A B f x op).
Proof. exact (@lem5804719 B (@neutral B op) (term58 A B f x op)). Qed.
Lemma lem5804721 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term38 A B x op f) = (term58 A B f x op).
Proof. exact (TRANS (@lem5804716 A B f x op h1) (@lem5804720 A B f x op)). Qed.
Lemma lem5804722 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term37 A B op x f) = (term58 A B f x op).
Proof. exact (TRANS (@lem5804663 A B x f op h1) (@lem5804721 A B f x op h1)). Qed.
Lemma lem5804723 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5804724 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term62 A B op x f) = (term63 A B f x op).
Proof. exact (MK_COMB (@lem5804723 B) (@lem5804722 A B f x op h1)). Qed.
Lemma lem5804725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5804726 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : ((term37 A B op x f) = (f x)) = ((term58 A B f x op) = (f x)).
Proof. exact (MK_COMB (@lem5804724 A B f x op h1) (@lem5804725 A B f x)). Qed.
Lemma lem5804729 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term64 A B op f) = (term65 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5804726 A B f x op h1)). Qed.
Lemma lem5804732 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5804733 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term66 A B op f) = (term67 A B op f).
Proof. exact (MK_COMB (@lem5804732 A) (@lem5804729 A B f op h1)). Qed.
Lemma lem5804740 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term68 A B op) = (term69 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5804733 A B f op h1)). Qed.
Lemma lem5804747 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5804748 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term26 A B op) = (term70 A B op).
Proof. exact (MK_COMB (@lem5804747 A B) (@lem5804740 A B op h1)). Qed.
Lemma lem5804759 {A B : Type'} (op : type1400 B) : term71 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5804748 A B op h0). Qed.
Lemma lem5804760 {A B : Type'} (op : type1400 B) : term72 A B op.
Proof. exact (@lem5804630 A B op (term70 A B op)). Qed.
Lemma lem5804761 {A B : Type'} (op : type1400 B) : (term73 A B op) = (term74 A B op).
Proof. exact (@lem5804760 A B op (@lem5804759 A B op)). Qed.
Lemma lem5804805 {A B : Type'} : (term75 A B) = (term76 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5804761 A B op)). Qed.
Lemma lem5804849 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5804850 {A B : Type'} : (term77 A B) = (term78 A B).
Proof. exact (MK_COMB (@lem5804849 B) (@lem5804805 A B)). Qed.
Lemma lem5804898 {A B : Type'} : (term78 A B) = (term77 A B).
Proof. exact (SYM (@lem5804850 A B)). Qed.
Lemma lem5804900 (p : Prop) : p = (term79 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5804901 {A B : Type'} : (term78 A B) = (term80 A B).
Proof. exact (@lem5804900 (term78 A B)). Qed.
Lemma lem5804902 {A B : Type'} : (term80 A B) = (term78 A B).
Proof. exact (SYM (@lem5804901 A B)). Qed.
Lemma lem5804903 {A B : Type'} (h1 : term81 A B) : term81 A B.
Proof. exact (h1). Qed.
Lemma lem5804904 {B : Type'} : term82 B.
Proof. exact (@lem5712802 B). Qed.
Lemma lem5804909 {A B : Type'} (h1 : term83 A B) : term83 A B.
Proof. exact (h1). Qed.
Lemma lem5804910 {A B : Type'} : term84 A B.
Proof. exact (fun h0 : term83 A B => @lem5804909 A B h0). Qed.
Lemma lem5804911 {A B : Type'} (h1 : term84 A B) : term84 A B.
Proof. exact (h1). Qed.
Lemma lem5804912 {A B : Type'} (h1 : term83 A B) : term83 A B.
Proof. exact (h1). Qed.
Lemma lem5804913 {A B : Type'} (h1 : term83 A B) (h2 : term84 A B) : term83 A B.
Proof. exact (@lem5804911 A B h2 (@lem5804912 A B h1)). Qed.
Lemma lem5804914 {A B : Type'} (h1 : term83 A B) : term85 A B.
Proof. exact (fun h0 : term84 A B => @lem5804913 A B h1 h0). Qed.
Lemma lem5804915 {A B : Type'} (h1 : term84 A B) : term84 A B.
Proof. exact (h1). Qed.
Lemma lem5804916 {A B : Type'} (h1 : term83 A B) (h2 : term84 A B) : term83 A B.
Proof. exact (@lem5804914 A B h1 (@lem5804915 A B h2)). Qed.
Lemma lem5804917 {A B : Type'} (h1 : term84 A B) : term84 A B.
Proof. exact (fun h0 : term83 A B => @lem5804916 A B h0 h1). Qed.
Lemma lem5804918 {A B : Type'} : term86 A B.
Proof. exact (fun h0 : term84 A B => @lem5804917 A B h0). Qed.
Lemma lem5804921 {A B : Type'} : term84 A B.
Proof. exact (@lem5804918 A B (@lem5804910 A B)). Qed.
Lemma lem5804922 {A B : Type'} : term84 A B.
Proof. exact (@lem5804921 A B). Qed.
Lemma lem5804940 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5804941 {B : Type'} : (term87 B) = (term88 B).
Proof. exact (@lem5804940 (term82 B)). Qed.
Lemma lem5804974 {A B : Type'} : (term89 A B) = (term89 A B).
Proof. exact (eq_refl (term89 A B)). Qed.
Lemma lem5804981 {A B : Type'} : (term83 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem5804974 A B) (@lem5804941 B)). Qed.
Lemma lem5804982 {B : Type'} (op : type1400 B) (x : B) : ((term91 B op x) = x) = ((term91 B op x) = x).
Proof. exact (eq_refl ((term91 B op x) = x)). Qed.
Lemma lem5804983 {B : Type'} (op : type1400 B) : (term92 B op) = (term92 B op).
Proof. exact (fun_ext (fun x : B => @lem5804982 B op x)). Qed.
Lemma lem5804984 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5804985 {B : Type'} (op : type1400 B) : (term93 B op) = (term93 B op).
Proof. exact (MK_COMB (@lem5804984 B) (@lem5804983 B op)). Qed.
Lemma lem5804986 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term94 B x op y z) = (term95 B op x y z)) = ((term94 B x op y z) = (term95 B op x y z)).
Proof. exact (eq_refl ((term94 B x op y z) = (term95 B op x y z))). Qed.
Lemma lem5804987 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term96 B op x y) = (term96 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5804986 B op x y z)). Qed.
Lemma lem5804988 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5804989 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term97 B op x y) = (term97 B op x y).
Proof. exact (MK_COMB (@lem5804988 B) (@lem5804987 B op x y)). Qed.
Lemma lem5804990 {B : Type'} (op : type1400 B) (x : B) : (term98 B op x) = (term98 B op x).
Proof. exact (fun_ext (fun y : B => @lem5804989 B op x y)). Qed.
Lemma lem5804991 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5804992 {B : Type'} (op : type1400 B) (x : B) : (term99 B op x) = (term99 B op x).
Proof. exact (MK_COMB (@lem5804991 B) (@lem5804990 B op x)). Qed.
Lemma lem5804993 {B : Type'} (op : type1400 B) : (term100 B op) = (term100 B op).
Proof. exact (fun_ext (fun x : B => @lem5804992 B op x)). Qed.
Lemma lem5804994 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5804995 {B : Type'} (op : type1400 B) : (term101 B op) = (term101 B op).
Proof. exact (MK_COMB (@lem5804994 B) (@lem5804993 B op)). Qed.
Lemma lem5804996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5804997 {B : Type'} (op : type1400 B) : (term102 B op) = (term102 B op).
Proof. exact (MK_COMB (@lem5804996) (@lem5804995 B op)). Qed.
Lemma lem5804998 {B : Type'} (op : type1400 B) : (term103 B op) = (term103 B op).
Proof. exact (MK_COMB (@lem5804997 B op) (@lem5804985 B op)). Qed.
Lemma lem5804999 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5805000 {B : Type'} (op : type1400 B) (x : B) : (term104 B op x) = (term104 B op x).
Proof. exact (fun_ext (fun y : B => @lem5804999 B op y x)). Qed.
Lemma lem5805001 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805002 {B : Type'} (op : type1400 B) (x : B) : (term105 B op x) = (term105 B op x).
Proof. exact (MK_COMB (@lem5805001 B) (@lem5805000 B op x)). Qed.
Lemma lem5805003 {B : Type'} (op : type1400 B) : (term106 B op) = (term106 B op).
Proof. exact (fun_ext (fun x : B => @lem5805002 B op x)). Qed.
Lemma lem5805004 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805005 {B : Type'} (op : type1400 B) : (term107 B op) = (term107 B op).
Proof. exact (MK_COMB (@lem5805004 B) (@lem5805003 B op)). Qed.
Lemma lem5805006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805007 {B : Type'} (op : type1400 B) : (term108 B op) = (term108 B op).
Proof. exact (MK_COMB (@lem5805006) (@lem5805005 B op)). Qed.
Lemma lem5805008 {B : Type'} (op : type1400 B) : (term109 B op) = (term109 B op).
Proof. exact (MK_COMB (@lem5805007 B op) (@lem5804998 B op)). Qed.
Lemma lem5805011 {B : Type'} (op : type1400 B) : (term110 B op) = (term110 B op).
Proof. exact (eq_refl (term110 B op)). Qed.
Lemma lem5805012 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term109 B op)) = ((@monoidal B op) = (term109 B op)).
Proof. exact (MK_COMB (@lem5805011 B op) (@lem5805008 B op)). Qed.
Lemma lem5805013 {B : Type'} : (term111 B) = (term111 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805012 B op)). Qed.
Lemma lem5805014 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805015 {B : Type'} : (term82 B) = (term82 B).
Proof. exact (MK_COMB (@lem5805014 B) (@lem5805013 B)). Qed.
Lemma lem5805016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805017 {B : Type'} : (term88 B) = (term88 B).
Proof. exact (MK_COMB (@lem5805016) (@lem5805015 B)). Qed.
Lemma lem5805018 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : ((term58 A B f x op) = (f x)) = ((term58 A B f x op) = (f x)).
Proof. exact (eq_refl ((term58 A B f x op) = (f x))). Qed.
Lemma lem5805019 {A B : Type'} (op : type1400 B) (f : A -> B) : (term65 A B op f) = (term65 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5805018 A B op f x)). Qed.
Lemma lem5805020 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5805021 {A B : Type'} (op : type1400 B) (f : A -> B) : (term67 A B op f) = (term67 A B op f).
Proof. exact (MK_COMB (@lem5805020 A) (@lem5805019 A B op f)). Qed.
Lemma lem5805022 {A B : Type'} (op : type1400 B) : (term69 A B op) = (term69 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5805021 A B op f)). Qed.
Lemma lem5805023 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5805024 {A B : Type'} (op : type1400 B) : (term70 A B op) = (term70 A B op).
Proof. exact (MK_COMB (@lem5805023 A B) (@lem5805022 A B op)). Qed.
Lemma lem5805027 {B : Type'} (op : type1400 B) : (term112 B op) = (term112 B op).
Proof. exact (eq_refl (term112 B op)). Qed.
Lemma lem5805028 {A B : Type'} (op : type1400 B) : (term74 A B op) = (term74 A B op).
Proof. exact (MK_COMB (@lem5805027 B op) (@lem5805024 A B op)). Qed.
Lemma lem5805029 {A B : Type'} : (term76 A B) = (term76 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805028 A B op)). Qed.
Lemma lem5805030 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805031 {A B : Type'} : (term78 A B) = (term78 A B).
Proof. exact (MK_COMB (@lem5805030 B) (@lem5805029 A B)). Qed.
Lemma lem5805032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805033 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (MK_COMB (@lem5805032) (@lem5805031 A B)). Qed.
Lemma lem5805034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5805035 {A B : Type'} : (term89 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem5805034) (@lem5805033 A B)). Qed.
Lemma lem5805036 {A B : Type'} : (term90 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem5805035 A B) (@lem5805017 B)). Qed.
Lemma lem5805107 {A B : Type'} : (term83 A B) = (term90 A B).
Proof. exact (TRANS (@lem5804981 A B) (@lem5805036 A B)). Qed.
Lemma lem5805108 {A B : Type'} : (term90 A B) = (term83 A B).
Proof. exact (SYM (@lem5805107 A B)). Qed.
Lemma lem5805109 {A B : Type'} (h1 : term81 A B) : term81 A B.
Proof. exact (h1). Qed.
Lemma lem5805110 {B : Type'} (h1 : term82 B) : term82 B.
Proof. exact (h1). Qed.
Lemma lem5805113 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5805114 {A B : Type'} (op : type1400 B) (f : A -> B) : (term115 A B op f) = (term116 A B op f).
Proof. exact (@lem5805113 A (term65 A B op f)). Qed.
Lemma lem5805115 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term117 A B op f x) = ((term58 A B f x op) = (f x)).
Proof. exact (eq_refl (term117 A B op f x)). Qed.
Lemma lem5805116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805118 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term118 A B op f x) = (term119 A B op f x).
Proof. exact (MK_COMB (@lem5805116) (@lem5805115 A B op f x)). Qed.
Lemma lem5805119 {A B : Type'} (op : type1400 B) (f : A -> B) : (term120 A B op f) = (term121 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5805118 A B op f x)). Qed.
Lemma lem5805120 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5805121 {A B : Type'} (op : type1400 B) (f : A -> B) : (term116 A B op f) = (term122 A B op f).
Proof. exact (MK_COMB (@lem5805120 A) (@lem5805119 A B op f)). Qed.
Lemma lem5805122 {A B : Type'} (op : type1400 B) (f : A -> B) : (term115 A B op f) = (term122 A B op f).
Proof. exact (TRANS (@lem5805114 A B op f) (@lem5805121 A B op f)). Qed.
Lemma lem5805123 {A B : Type'} (P : type572 A B) : (term123 A B P) = (term124 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem5805124 {A B : Type'} (op : type1400 B) : (term125 A B op) = (term126 A B op).
Proof. exact (@lem5805123 A B (term69 A B op)). Qed.
Lemma lem5805125 {A B : Type'} (op : type1400 B) (f : A -> B) : (term127 A B op f) = (term67 A B op f).
Proof. exact (eq_refl (term127 A B op f)). Qed.
Lemma lem5805126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805127 {A B : Type'} (op : type1400 B) (f : A -> B) : (term128 A B op f) = (term115 A B op f).
Proof. exact (MK_COMB (@lem5805126) (@lem5805125 A B op f)). Qed.
Lemma lem5805128 {A B : Type'} (op : type1400 B) (f : A -> B) : (term128 A B op f) = (term122 A B op f).
Proof. exact (TRANS (@lem5805127 A B op f) (@lem5805122 A B op f)). Qed.
Lemma lem5805129 {A B : Type'} (op : type1400 B) : (term129 A B op) = (term130 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5805128 A B op f)). Qed.
Lemma lem5805130 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5805131 {A B : Type'} (op : type1400 B) : (term126 A B op) = (term131 A B op).
Proof. exact (MK_COMB (@lem5805130 A B) (@lem5805129 A B op)). Qed.
Lemma lem5805132 {A B : Type'} (op : type1400 B) : (term125 A B op) = (term131 A B op).
Proof. exact (TRANS (@lem5805124 A B op) (@lem5805131 A B op)). Qed.
Lemma lem5805134 {B : Type'} (op : type1400 B) : (term132 B op) = (term132 B op).
Proof. exact (eq_refl (term132 B op)). Qed.
Lemma lem5805135 {A B : Type'} (op : type1400 B) : (term133 A B op) = (term134 A B op).
Proof. exact (MK_COMB (@lem5805134 B op) (@lem5805132 A B op)). Qed.
Lemma lem5805136 {A B : Type'} (op : type1400 B) : (term135 A B op) = (term133 A B op).
Proof. exact (@lem17362 (@monoidal B op) (term70 A B op)). Qed.
Lemma lem5805137 {A B : Type'} (op : type1400 B) : (term135 A B op) = (term134 A B op).
Proof. exact (TRANS (@lem5805136 A B op) (@lem5805135 A B op)). Qed.
Lemma lem5805138 {B : Type'} (P : type403 B) : (term136 B P) = (term137 B P).
Proof. exact (@lem18392 (type1400 B) P). Qed.
Lemma lem5805139 {A B : Type'} : (term81 A B) = (term138 A B).
Proof. exact (@lem5805138 B (term76 A B)). Qed.
Lemma lem5805140 {A B : Type'} (op : type1400 B) : (term139 A B op) = (term74 A B op).
Proof. exact (eq_refl (term139 A B op)). Qed.
Lemma lem5805141 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805142 {A B : Type'} (op : type1400 B) : (term140 A B op) = (term135 A B op).
Proof. exact (MK_COMB (@lem5805141) (@lem5805140 A B op)). Qed.
Lemma lem5805143 {A B : Type'} (op : type1400 B) : (term140 A B op) = (term134 A B op).
Proof. exact (TRANS (@lem5805142 A B op) (@lem5805137 A B op)). Qed.
Lemma lem5805144 {A B : Type'} : (term141 A B) = (term142 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805143 A B op)). Qed.
Lemma lem5805145 {B : Type'} : (@ex (B -> B -> B)) = (@ex (B -> B -> B)).
Proof. exact (eq_refl (@ex (B -> B -> B))). Qed.
Lemma lem5805146 {A B : Type'} : (term138 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem5805145 B) (@lem5805144 A B)). Qed.
Lemma lem5805147 {A B : Type'} : (term81 A B) = (term143 A B).
Proof. exact (TRANS (@lem5805139 A B) (@lem5805146 A B)). Qed.
Lemma lem5805186 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5805187 {A B : Type'} (P : Prop) (Q : type572 A B) : (term146 A B P Q) = (term147 A B P Q).
Proof. exact (@lem5805186 (A -> B) P Q). Qed.
Lemma lem5805188 {A B : Type'} (op : type1400 B) : (term148 A B op) = (term149 A B op).
Proof. exact (@lem5805187 A B (@monoidal B op) (term130 A B op)). Qed.
Lemma lem5805189 {A B : Type'} (op : type1400 B) (f : A -> B) : (term150 A B op f) = (term122 A B op f).
Proof. exact (eq_refl (term150 A B op f)). Qed.
Lemma lem5805190 {A B : Type'} (op : type1400 B) : (term151 A B op) = (term130 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5805189 A B op f)). Qed.
Lemma lem5805191 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5805192 {A B : Type'} (op : type1400 B) : (term152 A B op) = (term131 A B op).
Proof. exact (MK_COMB (@lem5805191 A B) (@lem5805190 A B op)). Qed.
Lemma lem5805193 {B : Type'} (op : type1400 B) : (term132 B op) = (term132 B op).
Proof. exact (eq_refl (term132 B op)). Qed.
Lemma lem5805194 {A B : Type'} (op : type1400 B) : (term148 A B op) = (term134 A B op).
Proof. exact (MK_COMB (@lem5805193 B op) (@lem5805192 A B op)). Qed.
Lemma lem5805195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805196 {A B : Type'} (op : type1400 B) : (term153 A B op) = (term154 A B op).
Proof. exact (MK_COMB (@lem5805195) (@lem5805194 A B op)). Qed.
Lemma lem5805197 {A B : Type'} (op : type1400 B) (f : A -> B) : (term150 A B op f) = (term122 A B op f).
Proof. exact (eq_refl (term150 A B op f)). Qed.
Lemma lem5805198 {B : Type'} (op : type1400 B) : (term132 B op) = (term132 B op).
Proof. exact (eq_refl (term132 B op)). Qed.
Lemma lem5805199 {A B : Type'} (op : type1400 B) (f : A -> B) : (term155 A B op f) = (term156 A B op f).
Proof. exact (MK_COMB (@lem5805198 B op) (@lem5805197 A B op f)). Qed.
Lemma lem5805200 {A B : Type'} (op : type1400 B) : (term157 A B op) = (term158 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5805199 A B op f)). Qed.
Lemma lem5805201 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5805202 {A B : Type'} (op : type1400 B) : (term149 A B op) = (term159 A B op).
Proof. exact (MK_COMB (@lem5805201 A B) (@lem5805200 A B op)). Qed.
Lemma lem5805203 {A B : Type'} (op : type1400 B) : ((term148 A B op) = (term149 A B op)) = ((term134 A B op) = (term159 A B op)).
Proof. exact (MK_COMB (@lem5805196 A B op) (@lem5805202 A B op)). Qed.
Lemma lem5805204 {A B : Type'} (op : type1400 B) : (term134 A B op) = (term159 A B op).
Proof. exact (EQ_MP (@lem5805203 A B op) (@lem5805188 A B op)). Qed.
Lemma lem5805206 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5805207 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem5805206 A P Q). Qed.
Lemma lem5805208 {A B : Type'} (op : type1400 B) (f : A -> B) : (term160 A B op f) = (term161 A B op f).
Proof. exact (@lem5805207 A (@monoidal B op) (term121 A B op f)). Qed.
Lemma lem5805209 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term162 A B op f x) = (term119 A B op f x).
Proof. exact (eq_refl (term162 A B op f x)). Qed.
Lemma lem5805210 {A B : Type'} (op : type1400 B) (f : A -> B) : (term163 A B op f) = (term121 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5805209 A B op f x)). Qed.
Lemma lem5805211 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5805212 {A B : Type'} (op : type1400 B) (f : A -> B) : (term164 A B op f) = (term122 A B op f).
Proof. exact (MK_COMB (@lem5805211 A) (@lem5805210 A B op f)). Qed.
Lemma lem5805213 {B : Type'} (op : type1400 B) : (term132 B op) = (term132 B op).
Proof. exact (eq_refl (term132 B op)). Qed.
Lemma lem5805214 {A B : Type'} (op : type1400 B) (f : A -> B) : (term160 A B op f) = (term156 A B op f).
Proof. exact (MK_COMB (@lem5805213 B op) (@lem5805212 A B op f)). Qed.
Lemma lem5805215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805216 {A B : Type'} (op : type1400 B) (f : A -> B) : (term165 A B op f) = (term166 A B op f).
Proof. exact (MK_COMB (@lem5805215) (@lem5805214 A B op f)). Qed.
Lemma lem5805217 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term162 A B op f x) = (term119 A B op f x).
Proof. exact (eq_refl (term162 A B op f x)). Qed.
Lemma lem5805218 {B : Type'} (op : type1400 B) : (term132 B op) = (term132 B op).
Proof. exact (eq_refl (term132 B op)). Qed.
Lemma lem5805219 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term167 A B op f x) = (term168 A B op f x).
Proof. exact (MK_COMB (@lem5805218 B op) (@lem5805217 A B op f x)). Qed.
Lemma lem5805220 {A B : Type'} (op : type1400 B) (f : A -> B) : (term169 A B op f) = (term170 A B op f).
Proof. exact (fun_ext (fun x : A => @lem5805219 A B op f x)). Qed.
Lemma lem5805221 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5805222 {A B : Type'} (op : type1400 B) (f : A -> B) : (term161 A B op f) = (term171 A B op f).
Proof. exact (MK_COMB (@lem5805221 A) (@lem5805220 A B op f)). Qed.
Lemma lem5805223 {A B : Type'} (op : type1400 B) (f : A -> B) : ((term160 A B op f) = (term161 A B op f)) = ((term156 A B op f) = (term171 A B op f)).
Proof. exact (MK_COMB (@lem5805216 A B op f) (@lem5805222 A B op f)). Qed.
Lemma lem5805224 {A B : Type'} (op : type1400 B) (f : A -> B) : (term156 A B op f) = (term171 A B op f).
Proof. exact (EQ_MP (@lem5805223 A B op f) (@lem5805208 A B op f)). Qed.
Lemma lem5805225 {A B : Type'} (op : type1400 B) : (term158 A B op) = (term172 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5805224 A B op f)). Qed.
Lemma lem5805226 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5805227 {A B : Type'} (op : type1400 B) : (term159 A B op) = (term173 A B op).
Proof. exact (MK_COMB (@lem5805226 A B) (@lem5805225 A B op)). Qed.
Lemma lem5805228 {A B : Type'} (op : type1400 B) : (term134 A B op) = (term173 A B op).
Proof. exact (TRANS (@lem5805204 A B op) (@lem5805227 A B op)). Qed.
Lemma lem5805229 {A B : Type'} : (term142 A B) = (term174 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805228 A B op)). Qed.
Lemma lem5805230 {B : Type'} : (@ex (B -> B -> B)) = (@ex (B -> B -> B)).
Proof. exact (eq_refl (@ex (B -> B -> B))). Qed.
Lemma lem5805232 {A B : Type'} : (term143 A B) = (term175 A B).
Proof. exact (MK_COMB (@lem5805230 B) (@lem5805229 A B)). Qed.
Lemma lem5805233 {A B : Type'} : (term81 A B) = (term175 A B).
Proof. exact (TRANS (@lem5805147 A B) (@lem5805232 A B)). Qed.
Lemma lem5805234 {A B : Type'} (h1 : term81 A B) : term175 A B.
Proof. exact (EQ_MP (@lem5805233 A B) (@lem5805109 A B h1)). Qed.
Lemma lem5805238 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5805239 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805240 {B : Type'} (op : type1400 B) (x : B) : (term176 B op x) = (term177 B op x).
Proof. exact (@lem5805239 B (term104 B op x)). Qed.
Lemma lem5805241 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term178 B op x y) = ((op x y) = (op y x)).
Proof. exact (eq_refl (term178 B op x y)). Qed.
Lemma lem5805242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805244 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term179 B op x y) = (term180 B op y x).
Proof. exact (MK_COMB (@lem5805242) (@lem5805241 B op y x)). Qed.
Lemma lem5805245 {B : Type'} (op : type1400 B) (x : B) : (term181 B op x) = (term182 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805244 B op y x)). Qed.
Lemma lem5805246 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805247 {B : Type'} (op : type1400 B) (x : B) : (term177 B op x) = (term183 B op x).
Proof. exact (MK_COMB (@lem5805246 B) (@lem5805245 B op x)). Qed.
Lemma lem5805248 {B : Type'} (op : type1400 B) (x : B) : (term176 B op x) = (term183 B op x).
Proof. exact (TRANS (@lem5805240 B op x) (@lem5805247 B op x)). Qed.
Lemma lem5805249 {B : Type'} (op : type1400 B) (x : B) : (term104 B op x) = (term104 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805238 B op y x)). Qed.
Lemma lem5805250 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805251 {B : Type'} (op : type1400 B) (x : B) : (term105 B op x) = (term105 B op x).
Proof. exact (MK_COMB (@lem5805250 B) (@lem5805249 B op x)). Qed.
Lemma lem5805252 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805253 {B : Type'} (op : type1400 B) : (term184 B op) = (term185 B op).
Proof. exact (@lem5805252 B (term106 B op)). Qed.
Lemma lem5805254 {B : Type'} (op : type1400 B) (x : B) : (term186 B op x) = (term105 B op x).
Proof. exact (eq_refl (term186 B op x)). Qed.
Lemma lem5805255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805256 {B : Type'} (op : type1400 B) (x : B) : (term187 B op x) = (term176 B op x).
Proof. exact (MK_COMB (@lem5805255) (@lem5805254 B op x)). Qed.
Lemma lem5805257 {B : Type'} (op : type1400 B) (x : B) : (term187 B op x) = (term183 B op x).
Proof. exact (TRANS (@lem5805256 B op x) (@lem5805248 B op x)). Qed.
Lemma lem5805258 {B : Type'} (op : type1400 B) : (term188 B op) = (term189 B op).
Proof. exact (fun_ext (fun x : B => @lem5805257 B op x)). Qed.
Lemma lem5805259 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805260 {B : Type'} (op : type1400 B) : (term185 B op) = (term190 B op).
Proof. exact (MK_COMB (@lem5805259 B) (@lem5805258 B op)). Qed.
Lemma lem5805261 {B : Type'} (op : type1400 B) : (term184 B op) = (term190 B op).
Proof. exact (TRANS (@lem5805253 B op) (@lem5805260 B op)). Qed.
Lemma lem5805262 {B : Type'} (op : type1400 B) : (term106 B op) = (term106 B op).
Proof. exact (fun_ext (fun x : B => @lem5805251 B op x)). Qed.
Lemma lem5805263 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805264 {B : Type'} (op : type1400 B) : (term107 B op) = (term107 B op).
Proof. exact (MK_COMB (@lem5805263 B) (@lem5805262 B op)). Qed.
Lemma lem5805266 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term94 B x op y z) = (term95 B op x y z)) = ((term94 B x op y z) = (term95 B op x y z)).
Proof. exact (eq_refl ((term94 B x op y z) = (term95 B op x y z))). Qed.
Lemma lem5805267 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805268 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term191 B op x y) = (term192 B op x y).
Proof. exact (@lem5805267 B (term96 B op x y)). Qed.
Lemma lem5805269 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term193 B op x y z) = ((term94 B x op y z) = (term95 B op x y z)).
Proof. exact (eq_refl (term193 B op x y z)). Qed.
Lemma lem5805270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805272 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term194 B op x y z) = (term195 B op x y z).
Proof. exact (MK_COMB (@lem5805270) (@lem5805269 B op x y z)). Qed.
Lemma lem5805273 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term196 B op x y) = (term197 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5805272 B op x y z)). Qed.
Lemma lem5805274 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805275 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term192 B op x y) = (term198 B op x y).
Proof. exact (MK_COMB (@lem5805274 B) (@lem5805273 B op x y)). Qed.
Lemma lem5805276 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term191 B op x y) = (term198 B op x y).
Proof. exact (TRANS (@lem5805268 B op x y) (@lem5805275 B op x y)). Qed.
Lemma lem5805277 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term96 B op x y) = (term96 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5805266 B op x y z)). Qed.
Lemma lem5805278 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805279 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term97 B op x y) = (term97 B op x y).
Proof. exact (MK_COMB (@lem5805278 B) (@lem5805277 B op x y)). Qed.
Lemma lem5805280 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805281 {B : Type'} (op : type1400 B) (x : B) : (term199 B op x) = (term200 B op x).
Proof. exact (@lem5805280 B (term98 B op x)). Qed.
Lemma lem5805282 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term201 B op x y) = (term97 B op x y).
Proof. exact (eq_refl (term201 B op x y)). Qed.
Lemma lem5805283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805284 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term202 B op x y) = (term191 B op x y).
Proof. exact (MK_COMB (@lem5805283) (@lem5805282 B op x y)). Qed.
Lemma lem5805285 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term202 B op x y) = (term198 B op x y).
Proof. exact (TRANS (@lem5805284 B op x y) (@lem5805276 B op x y)). Qed.
Lemma lem5805286 {B : Type'} (op : type1400 B) (x : B) : (term203 B op x) = (term204 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805285 B op x y)). Qed.
Lemma lem5805287 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805288 {B : Type'} (op : type1400 B) (x : B) : (term200 B op x) = (term205 B op x).
Proof. exact (MK_COMB (@lem5805287 B) (@lem5805286 B op x)). Qed.
Lemma lem5805289 {B : Type'} (op : type1400 B) (x : B) : (term199 B op x) = (term205 B op x).
Proof. exact (TRANS (@lem5805281 B op x) (@lem5805288 B op x)). Qed.
Lemma lem5805290 {B : Type'} (op : type1400 B) (x : B) : (term98 B op x) = (term98 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805279 B op x y)). Qed.
Lemma lem5805291 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805292 {B : Type'} (op : type1400 B) (x : B) : (term99 B op x) = (term99 B op x).
Proof. exact (MK_COMB (@lem5805291 B) (@lem5805290 B op x)). Qed.
Lemma lem5805293 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805294 {B : Type'} (op : type1400 B) : (term206 B op) = (term207 B op).
Proof. exact (@lem5805293 B (term100 B op)). Qed.
Lemma lem5805295 {B : Type'} (op : type1400 B) (x : B) : (term208 B op x) = (term99 B op x).
Proof. exact (eq_refl (term208 B op x)). Qed.
Lemma lem5805296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805297 {B : Type'} (op : type1400 B) (x : B) : (term209 B op x) = (term199 B op x).
Proof. exact (MK_COMB (@lem5805296) (@lem5805295 B op x)). Qed.
Lemma lem5805298 {B : Type'} (op : type1400 B) (x : B) : (term209 B op x) = (term205 B op x).
Proof. exact (TRANS (@lem5805297 B op x) (@lem5805289 B op x)). Qed.
Lemma lem5805299 {B : Type'} (op : type1400 B) : (term210 B op) = (term211 B op).
Proof. exact (fun_ext (fun x : B => @lem5805298 B op x)). Qed.
Lemma lem5805300 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805301 {B : Type'} (op : type1400 B) : (term207 B op) = (term212 B op).
Proof. exact (MK_COMB (@lem5805300 B) (@lem5805299 B op)). Qed.
Lemma lem5805302 {B : Type'} (op : type1400 B) : (term206 B op) = (term212 B op).
Proof. exact (TRANS (@lem5805294 B op) (@lem5805301 B op)). Qed.
Lemma lem5805303 {B : Type'} (op : type1400 B) : (term100 B op) = (term100 B op).
Proof. exact (fun_ext (fun x : B => @lem5805292 B op x)). Qed.
Lemma lem5805304 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805305 {B : Type'} (op : type1400 B) : (term101 B op) = (term101 B op).
Proof. exact (MK_COMB (@lem5805304 B) (@lem5805303 B op)). Qed.
Lemma lem5805307 {B : Type'} (op : type1400 B) (x : B) : ((term91 B op x) = x) = ((term91 B op x) = x).
Proof. exact (eq_refl ((term91 B op x) = x)). Qed.
Lemma lem5805308 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5805309 {B : Type'} (op : type1400 B) : (term213 B op) = (term214 B op).
Proof. exact (@lem5805308 B (term92 B op)). Qed.
Lemma lem5805310 {B : Type'} (op : type1400 B) (x : B) : (term215 B op x) = ((term91 B op x) = x).
Proof. exact (eq_refl (term215 B op x)). Qed.
Lemma lem5805311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5805313 {B : Type'} (op : type1400 B) (x : B) : (term216 B op x) = (term217 B op x).
Proof. exact (MK_COMB (@lem5805311) (@lem5805310 B op x)). Qed.
Lemma lem5805314 {B : Type'} (op : type1400 B) : (term218 B op) = (term219 B op).
Proof. exact (fun_ext (fun x : B => @lem5805313 B op x)). Qed.
Lemma lem5805315 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805316 {B : Type'} (op : type1400 B) : (term214 B op) = (term220 B op).
Proof. exact (MK_COMB (@lem5805315 B) (@lem5805314 B op)). Qed.
Lemma lem5805317 {B : Type'} (op : type1400 B) : (term213 B op) = (term220 B op).
Proof. exact (TRANS (@lem5805309 B op) (@lem5805316 B op)). Qed.
Lemma lem5805318 {B : Type'} (op : type1400 B) : (term92 B op) = (term92 B op).
Proof. exact (fun_ext (fun x : B => @lem5805307 B op x)). Qed.
Lemma lem5805319 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805320 {B : Type'} (op : type1400 B) : (term93 B op) = (term93 B op).
Proof. exact (MK_COMB (@lem5805319 B) (@lem5805318 B op)). Qed.
Lemma lem5805321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805322 {B : Type'} (op : type1400 B) : (term221 B op) = (term222 B op).
Proof. exact (MK_COMB (@lem5805321) (@lem5805302 B op)). Qed.
Lemma lem5805323 {B : Type'} (op : type1400 B) : (term223 B op) = (term224 B op).
Proof. exact (MK_COMB (@lem5805322 B op) (@lem5805317 B op)). Qed.
Lemma lem5805324 {B : Type'} (op : type1400 B) : (term225 B op) = (term223 B op).
Proof. exact (@lem17045 (term101 B op) (term93 B op)). Qed.
Lemma lem5805325 {B : Type'} (op : type1400 B) : (term225 B op) = (term224 B op).
Proof. exact (TRANS (@lem5805324 B op) (@lem5805323 B op)). Qed.
Lemma lem5805326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805327 {B : Type'} (op : type1400 B) : (term102 B op) = (term102 B op).
Proof. exact (MK_COMB (@lem5805326) (@lem5805305 B op)). Qed.
Lemma lem5805328 {B : Type'} (op : type1400 B) : (term103 B op) = (term103 B op).
Proof. exact (MK_COMB (@lem5805327 B op) (@lem5805320 B op)). Qed.
Lemma lem5805329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805330 {B : Type'} (op : type1400 B) : (term226 B op) = (term227 B op).
Proof. exact (MK_COMB (@lem5805329) (@lem5805261 B op)). Qed.
Lemma lem5805331 {B : Type'} (op : type1400 B) : (term228 B op) = (term229 B op).
Proof. exact (MK_COMB (@lem5805330 B op) (@lem5805325 B op)). Qed.
Lemma lem5805332 {B : Type'} (op : type1400 B) : (term230 B op) = (term228 B op).
Proof. exact (@lem17045 (term107 B op) (term103 B op)). Qed.
Lemma lem5805333 {B : Type'} (op : type1400 B) : (term230 B op) = (term229 B op).
Proof. exact (TRANS (@lem5805332 B op) (@lem5805331 B op)). Qed.
Lemma lem5805334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805335 {B : Type'} (op : type1400 B) : (term108 B op) = (term108 B op).
Proof. exact (MK_COMB (@lem5805334) (@lem5805264 B op)). Qed.
Lemma lem5805336 {B : Type'} (op : type1400 B) : (term109 B op) = (term109 B op).
Proof. exact (MK_COMB (@lem5805335 B op) (@lem5805328 B op)). Qed.
Lemma lem5805338 {B : Type'} (op : type1400 B) : (term231 B op) = (term231 B op).
Proof. exact (eq_refl (term231 B op)). Qed.
Lemma lem5805339 {B : Type'} (op : type1400 B) : (term232 B op) = (term232 B op).
Proof. exact (MK_COMB (@lem5805338 B op) (@lem5805336 B op)). Qed.
Lemma lem5805341 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805342 {B : Type'} (op : type1400 B) : (term234 B op) = (term235 B op).
Proof. exact (MK_COMB (@lem5805341 B op) (@lem5805333 B op)). Qed.
Lemma lem5805343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805344 {B : Type'} (op : type1400 B) : (term236 B op) = (term237 B op).
Proof. exact (MK_COMB (@lem5805343) (@lem5805342 B op)). Qed.
Lemma lem5805345 {B : Type'} (op : type1400 B) : (term238 B op) = (term239 B op).
Proof. exact (MK_COMB (@lem5805344 B op) (@lem5805339 B op)). Qed.
Lemma lem5805346 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term109 B op)) = (term238 B op).
Proof. exact (@lem17784 (@monoidal B op) (term109 B op)). Qed.
Lemma lem5805347 {B : Type'} (op : type1400 B) : ((@monoidal B op) = (term109 B op)) = (term239 B op).
Proof. exact (TRANS (@lem5805346 B op) (@lem5805345 B op)). Qed.
Lemma lem5805348 {B : Type'} : (term111 B) = (term240 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805347 B op)). Qed.
Lemma lem5805349 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805350 {B : Type'} : (term82 B) = (term241 B).
Proof. exact (MK_COMB (@lem5805349 B) (@lem5805348 B)). Qed.
Lemma lem5805352 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term242 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5805353 {B : Type'} (P : type403 B) (Q : type403 B) : (term244 B P Q) = (term245 B P Q).
Proof. exact (@lem5805352 (type1400 B) P Q). Qed.
Lemma lem5805354 {B : Type'} : (term246 B) = (term247 B).
Proof. exact (@lem5805353 B (term248 B) (term249 B)). Qed.
Lemma lem5805355 {B : Type'} (op : type1400 B) : (term250 B op) = (term235 B op).
Proof. exact (eq_refl (term250 B op)). Qed.
Lemma lem5805356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805357 {B : Type'} (op : type1400 B) : (term251 B op) = (term237 B op).
Proof. exact (MK_COMB (@lem5805356) (@lem5805355 B op)). Qed.
Lemma lem5805358 {B : Type'} (op : type1400 B) : (term252 B op) = (term232 B op).
Proof. exact (eq_refl (term252 B op)). Qed.
Lemma lem5805359 {B : Type'} (op : type1400 B) : (term253 B op) = (term239 B op).
Proof. exact (MK_COMB (@lem5805357 B op) (@lem5805358 B op)). Qed.
Lemma lem5805360 {B : Type'} : (term254 B) = (term240 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805359 B op)). Qed.
Lemma lem5805361 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805362 {B : Type'} : (term246 B) = (term241 B).
Proof. exact (MK_COMB (@lem5805361 B) (@lem5805360 B)). Qed.
Lemma lem5805363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805364 {B : Type'} : (term255 B) = (term256 B).
Proof. exact (MK_COMB (@lem5805363) (@lem5805362 B)). Qed.
Lemma lem5805365 {B : Type'} (op : type1400 B) : (term250 B op) = (term235 B op).
Proof. exact (eq_refl (term250 B op)). Qed.
Lemma lem5805366 {B : Type'} : (term257 B) = (term248 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805365 B op)). Qed.
Lemma lem5805367 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805368 {B : Type'} : (term258 B) = (term259 B).
Proof. exact (MK_COMB (@lem5805367 B) (@lem5805366 B)). Qed.
Lemma lem5805369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805370 {B : Type'} : (term260 B) = (term261 B).
Proof. exact (MK_COMB (@lem5805369) (@lem5805368 B)). Qed.
Lemma lem5805371 {B : Type'} (op : type1400 B) : (term252 B op) = (term232 B op).
Proof. exact (eq_refl (term252 B op)). Qed.
Lemma lem5805372 {B : Type'} : (term262 B) = (term249 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805371 B op)). Qed.
Lemma lem5805373 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805374 {B : Type'} : (term263 B) = (term264 B).
Proof. exact (MK_COMB (@lem5805373 B) (@lem5805372 B)). Qed.
Lemma lem5805375 {B : Type'} : (term247 B) = (term265 B).
Proof. exact (MK_COMB (@lem5805370 B) (@lem5805374 B)). Qed.
Lemma lem5805376 {B : Type'} : ((term246 B) = (term247 B)) = ((term241 B) = (term265 B)).
Proof. exact (MK_COMB (@lem5805364 B) (@lem5805375 B)). Qed.
Lemma lem5805377 {B : Type'} : (term241 B) = (term265 B).
Proof. exact (EQ_MP (@lem5805376 B) (@lem5805354 B)). Qed.
Lemma lem5805503 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5805504 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term266 B P Q) = (term267 B P Q).
Proof. exact (@lem5805503 B P Q). Qed.
Lemma lem5805505 {B : Type'} (op : type1400 B) : (term268 B op) = (term269 B op).
Proof. exact (@lem5805504 B (term211 B op) (term219 B op)). Qed.
Lemma lem5805506 {B : Type'} (op : type1400 B) (x : B) : (term270 B op x) = (term205 B op x).
Proof. exact (eq_refl (term270 B op x)). Qed.
Lemma lem5805507 {B : Type'} (op : type1400 B) : (term271 B op) = (term211 B op).
Proof. exact (fun_ext (fun x : B => @lem5805506 B op x)). Qed.
Lemma lem5805508 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805509 {B : Type'} (op : type1400 B) : (term272 B op) = (term212 B op).
Proof. exact (MK_COMB (@lem5805508 B) (@lem5805507 B op)). Qed.
Lemma lem5805510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805511 {B : Type'} (op : type1400 B) : (term273 B op) = (term222 B op).
Proof. exact (MK_COMB (@lem5805510) (@lem5805509 B op)). Qed.
Lemma lem5805512 {B : Type'} (op : type1400 B) (x : B) : (term274 B op x) = (term217 B op x).
Proof. exact (eq_refl (term274 B op x)). Qed.
Lemma lem5805513 {B : Type'} (op : type1400 B) : (term275 B op) = (term219 B op).
Proof. exact (fun_ext (fun x : B => @lem5805512 B op x)). Qed.
Lemma lem5805514 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805515 {B : Type'} (op : type1400 B) : (term276 B op) = (term220 B op).
Proof. exact (MK_COMB (@lem5805514 B) (@lem5805513 B op)). Qed.
Lemma lem5805516 {B : Type'} (op : type1400 B) : (term268 B op) = (term224 B op).
Proof. exact (MK_COMB (@lem5805511 B op) (@lem5805515 B op)). Qed.
Lemma lem5805517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805518 {B : Type'} (op : type1400 B) : (term277 B op) = (term278 B op).
Proof. exact (MK_COMB (@lem5805517) (@lem5805516 B op)). Qed.
Lemma lem5805519 {B : Type'} (op : type1400 B) (x : B) : (term270 B op x) = (term205 B op x).
Proof. exact (eq_refl (term270 B op x)). Qed.
Lemma lem5805520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805521 {B : Type'} (op : type1400 B) (x : B) : (term279 B op x) = (term280 B op x).
Proof. exact (MK_COMB (@lem5805520) (@lem5805519 B op x)). Qed.
Lemma lem5805522 {B : Type'} (op : type1400 B) (x : B) : (term274 B op x) = (term217 B op x).
Proof. exact (eq_refl (term274 B op x)). Qed.
Lemma lem5805523 {B : Type'} (op : type1400 B) (x : B) : (term281 B op x) = (term282 B op x).
Proof. exact (MK_COMB (@lem5805521 B op x) (@lem5805522 B op x)). Qed.
Lemma lem5805524 {B : Type'} (op : type1400 B) : (term283 B op) = (term284 B op).
Proof. exact (fun_ext (fun x : B => @lem5805523 B op x)). Qed.
Lemma lem5805525 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805526 {B : Type'} (op : type1400 B) : (term269 B op) = (term285 B op).
Proof. exact (MK_COMB (@lem5805525 B) (@lem5805524 B op)). Qed.
Lemma lem5805527 {B : Type'} (op : type1400 B) : ((term268 B op) = (term269 B op)) = ((term224 B op) = (term285 B op)).
Proof. exact (MK_COMB (@lem5805518 B op) (@lem5805526 B op)). Qed.
Lemma lem5805528 {B : Type'} (op : type1400 B) : (term224 B op) = (term285 B op).
Proof. exact (EQ_MP (@lem5805527 B op) (@lem5805505 B op)). Qed.
Lemma lem5805530 {A : Type'} (P : A -> Prop) (Q : Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5805531 {B : Type'} (P : B -> Prop) (Q : Prop) : (term286 B P Q) = (term287 B P Q).
Proof. exact (@lem5805530 B P Q). Qed.
Lemma lem5805532 {B : Type'} (op : type1400 B) (x : B) : (term288 B op x) = (term289 B op x).
Proof. exact (@lem5805531 B (term204 B op x) (term217 B op x)). Qed.
Lemma lem5805533 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term290 B op x y) = (term198 B op x y).
Proof. exact (eq_refl (term290 B op x y)). Qed.
Lemma lem5805534 {B : Type'} (op : type1400 B) (x : B) : (term291 B op x) = (term204 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805533 B op x y)). Qed.
Lemma lem5805535 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805536 {B : Type'} (op : type1400 B) (x : B) : (term292 B op x) = (term205 B op x).
Proof. exact (MK_COMB (@lem5805535 B) (@lem5805534 B op x)). Qed.
Lemma lem5805537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805538 {B : Type'} (op : type1400 B) (x : B) : (term293 B op x) = (term280 B op x).
Proof. exact (MK_COMB (@lem5805537) (@lem5805536 B op x)). Qed.
Lemma lem5805539 {B : Type'} (op : type1400 B) (x : B) : (term217 B op x) = (term217 B op x).
Proof. exact (eq_refl (term217 B op x)). Qed.
Lemma lem5805540 {B : Type'} (op : type1400 B) (x : B) : (term288 B op x) = (term282 B op x).
Proof. exact (MK_COMB (@lem5805538 B op x) (@lem5805539 B op x)). Qed.
Lemma lem5805541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805542 {B : Type'} (op : type1400 B) (x : B) : (term294 B op x) = (term295 B op x).
Proof. exact (MK_COMB (@lem5805541) (@lem5805540 B op x)). Qed.
Lemma lem5805543 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term290 B op x y) = (term198 B op x y).
Proof. exact (eq_refl (term290 B op x y)). Qed.
Lemma lem5805544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805545 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term296 B op x y) = (term297 B op x y).
Proof. exact (MK_COMB (@lem5805544) (@lem5805543 B op x y)). Qed.
Lemma lem5805546 {B : Type'} (op : type1400 B) (x : B) : (term217 B op x) = (term217 B op x).
Proof. exact (eq_refl (term217 B op x)). Qed.
Lemma lem5805547 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term298 B y op x) = (term299 B y op x).
Proof. exact (MK_COMB (@lem5805545 B op x y) (@lem5805546 B op x)). Qed.
Lemma lem5805548 {B : Type'} (op : type1400 B) (x : B) : (term300 B op x) = (term301 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805547 B y op x)). Qed.
Lemma lem5805549 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805550 {B : Type'} (op : type1400 B) (x : B) : (term289 B op x) = (term302 B op x).
Proof. exact (MK_COMB (@lem5805549 B) (@lem5805548 B op x)). Qed.
Lemma lem5805551 {B : Type'} (op : type1400 B) (x : B) : ((term288 B op x) = (term289 B op x)) = ((term282 B op x) = (term302 B op x)).
Proof. exact (MK_COMB (@lem5805542 B op x) (@lem5805550 B op x)). Qed.
Lemma lem5805552 {B : Type'} (op : type1400 B) (x : B) : (term282 B op x) = (term302 B op x).
Proof. exact (EQ_MP (@lem5805551 B op x) (@lem5805532 B op x)). Qed.
Lemma lem5805554 {A : Type'} (P : A -> Prop) (Q : Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5805555 {B : Type'} (P : B -> Prop) (Q : Prop) : (term286 B P Q) = (term287 B P Q).
Proof. exact (@lem5805554 B P Q). Qed.
Lemma lem5805556 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term303 B y op x) = (term304 B y op x).
Proof. exact (@lem5805555 B (term197 B op x y) (term217 B op x)). Qed.
Lemma lem5805557 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term305 B op x y z) = (term195 B op x y z).
Proof. exact (eq_refl (term305 B op x y z)). Qed.
Lemma lem5805558 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term306 B op x y) = (term197 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5805557 B op x y z)). Qed.
Lemma lem5805559 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805560 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term307 B op x y) = (term198 B op x y).
Proof. exact (MK_COMB (@lem5805559 B) (@lem5805558 B op x y)). Qed.
Lemma lem5805561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805562 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term308 B op x y) = (term297 B op x y).
Proof. exact (MK_COMB (@lem5805561) (@lem5805560 B op x y)). Qed.
Lemma lem5805563 {B : Type'} (op : type1400 B) (x : B) : (term217 B op x) = (term217 B op x).
Proof. exact (eq_refl (term217 B op x)). Qed.
Lemma lem5805564 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term303 B y op x) = (term299 B y op x).
Proof. exact (MK_COMB (@lem5805562 B op x y) (@lem5805563 B op x)). Qed.
Lemma lem5805565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805566 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term309 B y op x) = (term310 B y op x).
Proof. exact (MK_COMB (@lem5805565) (@lem5805564 B y op x)). Qed.
Lemma lem5805567 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term305 B op x y z) = (term195 B op x y z).
Proof. exact (eq_refl (term305 B op x y z)). Qed.
Lemma lem5805568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805569 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term311 B op x y z) = (term312 B op x y z).
Proof. exact (MK_COMB (@lem5805568) (@lem5805567 B op x y z)). Qed.
Lemma lem5805570 {B : Type'} (op : type1400 B) (x : B) : (term217 B op x) = (term217 B op x).
Proof. exact (eq_refl (term217 B op x)). Qed.
Lemma lem5805571 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term313 B y z op x) = (term314 B y z op x).
Proof. exact (MK_COMB (@lem5805569 B op x y z) (@lem5805570 B op x)). Qed.
Lemma lem5805572 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term315 B y op x) = (term316 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5805571 B y z op x)). Qed.
Lemma lem5805573 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805574 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term304 B y op x) = (term317 B y op x).
Proof. exact (MK_COMB (@lem5805573 B) (@lem5805572 B y op x)). Qed.
Lemma lem5805575 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term303 B y op x) = (term304 B y op x)) = ((term299 B y op x) = (term317 B y op x)).
Proof. exact (MK_COMB (@lem5805566 B y op x) (@lem5805574 B y op x)). Qed.
Lemma lem5805576 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term299 B y op x) = (term317 B y op x).
Proof. exact (EQ_MP (@lem5805575 B y op x) (@lem5805556 B y op x)). Qed.
Lemma lem5805577 {B : Type'} (op : type1400 B) (x : B) : (term301 B op x) = (term318 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805576 B y op x)). Qed.
Lemma lem5805578 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805579 {B : Type'} (op : type1400 B) (x : B) : (term302 B op x) = (term319 B op x).
Proof. exact (MK_COMB (@lem5805578 B) (@lem5805577 B op x)). Qed.
Lemma lem5805580 {B : Type'} (op : type1400 B) (x : B) : (term282 B op x) = (term319 B op x).
Proof. exact (TRANS (@lem5805552 B op x) (@lem5805579 B op x)). Qed.
Lemma lem5805581 {B : Type'} (op : type1400 B) : (term284 B op) = (term320 B op).
Proof. exact (fun_ext (fun x : B => @lem5805580 B op x)). Qed.
Lemma lem5805582 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805583 {B : Type'} (op : type1400 B) : (term285 B op) = (term321 B op).
Proof. exact (MK_COMB (@lem5805582 B) (@lem5805581 B op)). Qed.
Lemma lem5805584 {B : Type'} (op : type1400 B) : (term224 B op) = (term321 B op).
Proof. exact (TRANS (@lem5805528 B op) (@lem5805583 B op)). Qed.
Lemma lem5805585 {B : Type'} (op : type1400 B) : (term227 B op) = (term227 B op).
Proof. exact (eq_refl (term227 B op)). Qed.
Lemma lem5805586 {B : Type'} (op : type1400 B) : (term229 B op) = (term322 B op).
Proof. exact (MK_COMB (@lem5805585 B op) (@lem5805584 B op)). Qed.
Lemma lem5805588 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5805589 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term266 B P Q) = (term267 B P Q).
Proof. exact (@lem5805588 B P Q). Qed.
Lemma lem5805590 {B : Type'} (op : type1400 B) : (term323 B op) = (term324 B op).
Proof. exact (@lem5805589 B (term189 B op) (term320 B op)). Qed.
Lemma lem5805591 {B : Type'} (op : type1400 B) (x : B) : (term325 B op x) = (term183 B op x).
Proof. exact (eq_refl (term325 B op x)). Qed.
Lemma lem5805592 {B : Type'} (op : type1400 B) : (term326 B op) = (term189 B op).
Proof. exact (fun_ext (fun x : B => @lem5805591 B op x)). Qed.
Lemma lem5805593 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805594 {B : Type'} (op : type1400 B) : (term327 B op) = (term190 B op).
Proof. exact (MK_COMB (@lem5805593 B) (@lem5805592 B op)). Qed.
Lemma lem5805595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805596 {B : Type'} (op : type1400 B) : (term328 B op) = (term227 B op).
Proof. exact (MK_COMB (@lem5805595) (@lem5805594 B op)). Qed.
Lemma lem5805597 {B : Type'} (op : type1400 B) (x : B) : (term329 B op x) = (term319 B op x).
Proof. exact (eq_refl (term329 B op x)). Qed.
Lemma lem5805598 {B : Type'} (op : type1400 B) : (term330 B op) = (term320 B op).
Proof. exact (fun_ext (fun x : B => @lem5805597 B op x)). Qed.
Lemma lem5805599 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805600 {B : Type'} (op : type1400 B) : (term331 B op) = (term321 B op).
Proof. exact (MK_COMB (@lem5805599 B) (@lem5805598 B op)). Qed.
Lemma lem5805601 {B : Type'} (op : type1400 B) : (term323 B op) = (term322 B op).
Proof. exact (MK_COMB (@lem5805596 B op) (@lem5805600 B op)). Qed.
Lemma lem5805602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805603 {B : Type'} (op : type1400 B) : (term332 B op) = (term333 B op).
Proof. exact (MK_COMB (@lem5805602) (@lem5805601 B op)). Qed.
Lemma lem5805604 {B : Type'} (op : type1400 B) (x : B) : (term325 B op x) = (term183 B op x).
Proof. exact (eq_refl (term325 B op x)). Qed.
Lemma lem5805605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805606 {B : Type'} (op : type1400 B) (x : B) : (term334 B op x) = (term335 B op x).
Proof. exact (MK_COMB (@lem5805605) (@lem5805604 B op x)). Qed.
Lemma lem5805607 {B : Type'} (op : type1400 B) (x : B) : (term329 B op x) = (term319 B op x).
Proof. exact (eq_refl (term329 B op x)). Qed.
Lemma lem5805608 {B : Type'} (op : type1400 B) (x : B) : (term336 B op x) = (term337 B op x).
Proof. exact (MK_COMB (@lem5805606 B op x) (@lem5805607 B op x)). Qed.
Lemma lem5805609 {B : Type'} (op : type1400 B) : (term338 B op) = (term339 B op).
Proof. exact (fun_ext (fun x : B => @lem5805608 B op x)). Qed.
Lemma lem5805610 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805611 {B : Type'} (op : type1400 B) : (term324 B op) = (term340 B op).
Proof. exact (MK_COMB (@lem5805610 B) (@lem5805609 B op)). Qed.
Lemma lem5805612 {B : Type'} (op : type1400 B) : ((term323 B op) = (term324 B op)) = ((term322 B op) = (term340 B op)).
Proof. exact (MK_COMB (@lem5805603 B op) (@lem5805611 B op)). Qed.
Lemma lem5805613 {B : Type'} (op : type1400 B) : (term322 B op) = (term340 B op).
Proof. exact (EQ_MP (@lem5805612 B op) (@lem5805590 B op)). Qed.
Lemma lem5805615 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5805616 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term266 B P Q) = (term267 B P Q).
Proof. exact (@lem5805615 B P Q). Qed.
Lemma lem5805617 {B : Type'} (op : type1400 B) (x : B) : (term341 B op x) = (term342 B op x).
Proof. exact (@lem5805616 B (term182 B op x) (term318 B op x)). Qed.
Lemma lem5805618 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term343 B op x y) = (term180 B op y x).
Proof. exact (eq_refl (term343 B op x y)). Qed.
Lemma lem5805619 {B : Type'} (op : type1400 B) (x : B) : (term344 B op x) = (term182 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805618 B op y x)). Qed.
Lemma lem5805620 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805621 {B : Type'} (op : type1400 B) (x : B) : (term345 B op x) = (term183 B op x).
Proof. exact (MK_COMB (@lem5805620 B) (@lem5805619 B op x)). Qed.
Lemma lem5805622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805623 {B : Type'} (op : type1400 B) (x : B) : (term346 B op x) = (term335 B op x).
Proof. exact (MK_COMB (@lem5805622) (@lem5805621 B op x)). Qed.
Lemma lem5805624 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term347 B op x y) = (term317 B y op x).
Proof. exact (eq_refl (term347 B op x y)). Qed.
Lemma lem5805625 {B : Type'} (op : type1400 B) (x : B) : (term348 B op x) = (term318 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805624 B y op x)). Qed.
Lemma lem5805626 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805627 {B : Type'} (op : type1400 B) (x : B) : (term349 B op x) = (term319 B op x).
Proof. exact (MK_COMB (@lem5805626 B) (@lem5805625 B op x)). Qed.
Lemma lem5805628 {B : Type'} (op : type1400 B) (x : B) : (term341 B op x) = (term337 B op x).
Proof. exact (MK_COMB (@lem5805623 B op x) (@lem5805627 B op x)). Qed.
Lemma lem5805629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805630 {B : Type'} (op : type1400 B) (x : B) : (term350 B op x) = (term351 B op x).
Proof. exact (MK_COMB (@lem5805629) (@lem5805628 B op x)). Qed.
Lemma lem5805631 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term343 B op x y) = (term180 B op y x).
Proof. exact (eq_refl (term343 B op x y)). Qed.
Lemma lem5805632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5805633 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term352 B op x y) = (term353 B op y x).
Proof. exact (MK_COMB (@lem5805632) (@lem5805631 B op y x)). Qed.
Lemma lem5805634 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term347 B op x y) = (term317 B y op x).
Proof. exact (eq_refl (term347 B op x y)). Qed.
Lemma lem5805635 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term354 B op x y) = (term355 B y op x).
Proof. exact (MK_COMB (@lem5805633 B op y x) (@lem5805634 B y op x)). Qed.
Lemma lem5805636 {B : Type'} (op : type1400 B) (x : B) : (term356 B op x) = (term357 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805635 B y op x)). Qed.
Lemma lem5805637 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805638 {B : Type'} (op : type1400 B) (x : B) : (term342 B op x) = (term358 B op x).
Proof. exact (MK_COMB (@lem5805637 B) (@lem5805636 B op x)). Qed.
Lemma lem5805639 {B : Type'} (op : type1400 B) (x : B) : ((term341 B op x) = (term342 B op x)) = ((term337 B op x) = (term358 B op x)).
Proof. exact (MK_COMB (@lem5805630 B op x) (@lem5805638 B op x)). Qed.
Lemma lem5805640 {B : Type'} (op : type1400 B) (x : B) : (term337 B op x) = (term358 B op x).
Proof. exact (EQ_MP (@lem5805639 B op x) (@lem5805617 B op x)). Qed.
Lemma lem5805642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5805643 {B : Type'} (P : Prop) (Q : B -> Prop) : (term359 B P Q) = (term360 B P Q).
Proof. exact (@lem5805642 B P Q). Qed.
Lemma lem5805644 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term361 B y op x) = (term362 B y op x).
Proof. exact (@lem5805643 B (term180 B op y x) (term316 B y op x)). Qed.
Lemma lem5805645 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term363 B y op x z) = (term314 B y z op x).
Proof. exact (eq_refl (term363 B y op x z)). Qed.
Lemma lem5805646 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term364 B y op x) = (term316 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5805645 B y z op x)). Qed.
Lemma lem5805647 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805648 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term365 B y op x) = (term317 B y op x).
Proof. exact (MK_COMB (@lem5805647 B) (@lem5805646 B y op x)). Qed.
Lemma lem5805649 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term353 B op y x) = (term353 B op y x).
Proof. exact (eq_refl (term353 B op y x)). Qed.
Lemma lem5805650 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term361 B y op x) = (term355 B y op x).
Proof. exact (MK_COMB (@lem5805649 B op y x) (@lem5805648 B y op x)). Qed.
Lemma lem5805651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805652 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term366 B y op x) = (term367 B y op x).
Proof. exact (MK_COMB (@lem5805651) (@lem5805650 B y op x)). Qed.
Lemma lem5805653 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term363 B y op x z) = (term314 B y z op x).
Proof. exact (eq_refl (term363 B y op x z)). Qed.
Lemma lem5805654 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term353 B op y x) = (term353 B op y x).
Proof. exact (eq_refl (term353 B op y x)). Qed.
Lemma lem5805655 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term368 B y op x z) = (term369 B y z op x).
Proof. exact (MK_COMB (@lem5805654 B op y x) (@lem5805653 B y z op x)). Qed.
Lemma lem5805656 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term370 B y op x) = (term371 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5805655 B y z op x)). Qed.
Lemma lem5805657 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805658 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term362 B y op x) = (term372 B y op x).
Proof. exact (MK_COMB (@lem5805657 B) (@lem5805656 B y op x)). Qed.
Lemma lem5805659 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term361 B y op x) = (term362 B y op x)) = ((term355 B y op x) = (term372 B y op x)).
Proof. exact (MK_COMB (@lem5805652 B y op x) (@lem5805658 B y op x)). Qed.
Lemma lem5805660 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term355 B y op x) = (term372 B y op x).
Proof. exact (EQ_MP (@lem5805659 B y op x) (@lem5805644 B y op x)). Qed.
Lemma lem5805661 {B : Type'} (op : type1400 B) (x : B) : (term357 B op x) = (term373 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805660 B y op x)). Qed.
Lemma lem5805662 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805663 {B : Type'} (op : type1400 B) (x : B) : (term358 B op x) = (term374 B op x).
Proof. exact (MK_COMB (@lem5805662 B) (@lem5805661 B op x)). Qed.
Lemma lem5805664 {B : Type'} (op : type1400 B) (x : B) : (term337 B op x) = (term374 B op x).
Proof. exact (TRANS (@lem5805640 B op x) (@lem5805663 B op x)). Qed.
Lemma lem5805665 {B : Type'} (op : type1400 B) : (term339 B op) = (term375 B op).
Proof. exact (fun_ext (fun x : B => @lem5805664 B op x)). Qed.
Lemma lem5805666 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805667 {B : Type'} (op : type1400 B) : (term340 B op) = (term376 B op).
Proof. exact (MK_COMB (@lem5805666 B) (@lem5805665 B op)). Qed.
Lemma lem5805668 {B : Type'} (op : type1400 B) : (term322 B op) = (term376 B op).
Proof. exact (TRANS (@lem5805613 B op) (@lem5805667 B op)). Qed.
Lemma lem5805669 {B : Type'} (op : type1400 B) : (term229 B op) = (term376 B op).
Proof. exact (TRANS (@lem5805586 B op) (@lem5805668 B op)). Qed.
Lemma lem5805670 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805671 {B : Type'} (op : type1400 B) : (term235 B op) = (term377 B op).
Proof. exact (MK_COMB (@lem5805670 B op) (@lem5805669 B op)). Qed.
Lemma lem5805673 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5805674 {B : Type'} (P : Prop) (Q : B -> Prop) : (term359 B P Q) = (term360 B P Q).
Proof. exact (@lem5805673 B P Q). Qed.
Lemma lem5805675 {B : Type'} (op : type1400 B) : (term378 B op) = (term379 B op).
Proof. exact (@lem5805674 B (@monoidal B op) (term375 B op)). Qed.
Lemma lem5805676 {B : Type'} (op : type1400 B) (x : B) : (term380 B op x) = (term374 B op x).
Proof. exact (eq_refl (term380 B op x)). Qed.
Lemma lem5805677 {B : Type'} (op : type1400 B) : (term381 B op) = (term375 B op).
Proof. exact (fun_ext (fun x : B => @lem5805676 B op x)). Qed.
Lemma lem5805678 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805679 {B : Type'} (op : type1400 B) : (term382 B op) = (term376 B op).
Proof. exact (MK_COMB (@lem5805678 B) (@lem5805677 B op)). Qed.
Lemma lem5805680 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805681 {B : Type'} (op : type1400 B) : (term378 B op) = (term377 B op).
Proof. exact (MK_COMB (@lem5805680 B op) (@lem5805679 B op)). Qed.
Lemma lem5805682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805683 {B : Type'} (op : type1400 B) : (term383 B op) = (term384 B op).
Proof. exact (MK_COMB (@lem5805682) (@lem5805681 B op)). Qed.
Lemma lem5805684 {B : Type'} (op : type1400 B) (x : B) : (term380 B op x) = (term374 B op x).
Proof. exact (eq_refl (term380 B op x)). Qed.
Lemma lem5805685 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805686 {B : Type'} (op : type1400 B) (x : B) : (term385 B op x) = (term386 B op x).
Proof. exact (MK_COMB (@lem5805685 B op) (@lem5805684 B op x)). Qed.
Lemma lem5805687 {B : Type'} (op : type1400 B) : (term387 B op) = (term388 B op).
Proof. exact (fun_ext (fun x : B => @lem5805686 B op x)). Qed.
Lemma lem5805688 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805689 {B : Type'} (op : type1400 B) : (term379 B op) = (term389 B op).
Proof. exact (MK_COMB (@lem5805688 B) (@lem5805687 B op)). Qed.
Lemma lem5805690 {B : Type'} (op : type1400 B) : ((term378 B op) = (term379 B op)) = ((term377 B op) = (term389 B op)).
Proof. exact (MK_COMB (@lem5805683 B op) (@lem5805689 B op)). Qed.
Lemma lem5805691 {B : Type'} (op : type1400 B) : (term377 B op) = (term389 B op).
Proof. exact (EQ_MP (@lem5805690 B op) (@lem5805675 B op)). Qed.
Lemma lem5805693 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5805694 {B : Type'} (P : Prop) (Q : B -> Prop) : (term359 B P Q) = (term360 B P Q).
Proof. exact (@lem5805693 B P Q). Qed.
Lemma lem5805695 {B : Type'} (op : type1400 B) (x : B) : (term390 B op x) = (term391 B op x).
Proof. exact (@lem5805694 B (@monoidal B op) (term373 B op x)). Qed.
Lemma lem5805696 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term392 B op x y) = (term372 B y op x).
Proof. exact (eq_refl (term392 B op x y)). Qed.
Lemma lem5805697 {B : Type'} (op : type1400 B) (x : B) : (term393 B op x) = (term373 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805696 B y op x)). Qed.
Lemma lem5805698 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805699 {B : Type'} (op : type1400 B) (x : B) : (term394 B op x) = (term374 B op x).
Proof. exact (MK_COMB (@lem5805698 B) (@lem5805697 B op x)). Qed.
Lemma lem5805700 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805701 {B : Type'} (op : type1400 B) (x : B) : (term390 B op x) = (term386 B op x).
Proof. exact (MK_COMB (@lem5805700 B op) (@lem5805699 B op x)). Qed.
Lemma lem5805702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805703 {B : Type'} (op : type1400 B) (x : B) : (term395 B op x) = (term396 B op x).
Proof. exact (MK_COMB (@lem5805702) (@lem5805701 B op x)). Qed.
Lemma lem5805704 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term392 B op x y) = (term372 B y op x).
Proof. exact (eq_refl (term392 B op x y)). Qed.
Lemma lem5805705 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805706 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term397 B op x y) = (term398 B y op x).
Proof. exact (MK_COMB (@lem5805705 B op) (@lem5805704 B y op x)). Qed.
Lemma lem5805707 {B : Type'} (op : type1400 B) (x : B) : (term399 B op x) = (term400 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805706 B y op x)). Qed.
Lemma lem5805708 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805709 {B : Type'} (op : type1400 B) (x : B) : (term391 B op x) = (term401 B op x).
Proof. exact (MK_COMB (@lem5805708 B) (@lem5805707 B op x)). Qed.
Lemma lem5805710 {B : Type'} (op : type1400 B) (x : B) : ((term390 B op x) = (term391 B op x)) = ((term386 B op x) = (term401 B op x)).
Proof. exact (MK_COMB (@lem5805703 B op x) (@lem5805709 B op x)). Qed.
Lemma lem5805711 {B : Type'} (op : type1400 B) (x : B) : (term386 B op x) = (term401 B op x).
Proof. exact (EQ_MP (@lem5805710 B op x) (@lem5805695 B op x)). Qed.
Lemma lem5805713 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5805714 {B : Type'} (P : Prop) (Q : B -> Prop) : (term359 B P Q) = (term360 B P Q).
Proof. exact (@lem5805713 B P Q). Qed.
Lemma lem5805715 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term402 B y op x) = (term403 B y op x).
Proof. exact (@lem5805714 B (@monoidal B op) (term371 B y op x)). Qed.
Lemma lem5805716 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term404 B y op x z) = (term369 B y z op x).
Proof. exact (eq_refl (term404 B y op x z)). Qed.
Lemma lem5805717 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term405 B y op x) = (term371 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5805716 B y z op x)). Qed.
Lemma lem5805718 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805719 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term406 B y op x) = (term372 B y op x).
Proof. exact (MK_COMB (@lem5805718 B) (@lem5805717 B y op x)). Qed.
Lemma lem5805720 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805721 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term402 B y op x) = (term398 B y op x).
Proof. exact (MK_COMB (@lem5805720 B op) (@lem5805719 B y op x)). Qed.
Lemma lem5805722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805723 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term407 B y op x) = (term408 B y op x).
Proof. exact (MK_COMB (@lem5805722) (@lem5805721 B y op x)). Qed.
Lemma lem5805724 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term404 B y op x z) = (term369 B y z op x).
Proof. exact (eq_refl (term404 B y op x z)). Qed.
Lemma lem5805725 {B : Type'} (op : type1400 B) : (term233 B op) = (term233 B op).
Proof. exact (eq_refl (term233 B op)). Qed.
Lemma lem5805726 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term409 B y op x z) = (term410 B y z op x).
Proof. exact (MK_COMB (@lem5805725 B op) (@lem5805724 B y z op x)). Qed.
Lemma lem5805727 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term411 B y op x) = (term412 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5805726 B y z op x)). Qed.
Lemma lem5805728 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805729 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term403 B y op x) = (term413 B y op x).
Proof. exact (MK_COMB (@lem5805728 B) (@lem5805727 B y op x)). Qed.
Lemma lem5805730 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term402 B y op x) = (term403 B y op x)) = ((term398 B y op x) = (term413 B y op x)).
Proof. exact (MK_COMB (@lem5805723 B y op x) (@lem5805729 B y op x)). Qed.
Lemma lem5805731 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term398 B y op x) = (term413 B y op x).
Proof. exact (EQ_MP (@lem5805730 B y op x) (@lem5805715 B y op x)). Qed.
Lemma lem5805732 {B : Type'} (op : type1400 B) (x : B) : (term400 B op x) = (term414 B op x).
Proof. exact (fun_ext (fun y : B => @lem5805731 B y op x)). Qed.
Lemma lem5805733 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805734 {B : Type'} (op : type1400 B) (x : B) : (term401 B op x) = (term415 B op x).
Proof. exact (MK_COMB (@lem5805733 B) (@lem5805732 B op x)). Qed.
Lemma lem5805735 {B : Type'} (op : type1400 B) (x : B) : (term386 B op x) = (term415 B op x).
Proof. exact (TRANS (@lem5805711 B op x) (@lem5805734 B op x)). Qed.
Lemma lem5805736 {B : Type'} (op : type1400 B) : (term388 B op) = (term416 B op).
Proof. exact (fun_ext (fun x : B => @lem5805735 B op x)). Qed.
Lemma lem5805737 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805738 {B : Type'} (op : type1400 B) : (term389 B op) = (term417 B op).
Proof. exact (MK_COMB (@lem5805737 B) (@lem5805736 B op)). Qed.
Lemma lem5805739 {B : Type'} (op : type1400 B) : (term377 B op) = (term417 B op).
Proof. exact (TRANS (@lem5805691 B op) (@lem5805738 B op)). Qed.
Lemma lem5805740 {B : Type'} (op : type1400 B) : (term235 B op) = (term417 B op).
Proof. exact (TRANS (@lem5805671 B op) (@lem5805739 B op)). Qed.
Lemma lem5805741 {B : Type'} : (term248 B) = (term418 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805740 B op)). Qed.
Lemma lem5805742 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805743 {B : Type'} : (term259 B) = (term419 B).
Proof. exact (MK_COMB (@lem5805742 B) (@lem5805741 B)). Qed.
Lemma lem5805745 {A B : Type'} (P : type1413 A B) : (term420 A B P) = (term421 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5805746 {B : Type'} (P : type401 B) : (term422 B P) = (term423 B P).
Proof. exact (@lem5805745 (type1400 B) B P). Qed.
Lemma lem5805747 {B : Type'} : (term424 B) = (term425 B).
Proof. exact (@lem5805746 B (term426 B)). Qed.
Lemma lem5805748 {B : Type'} (op : type1400 B) : (term427 B op) = (term416 B op).
Proof. exact (eq_refl (term427 B op)). Qed.
Lemma lem5805749 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5805750 {B : Type'} (op : type1400 B) (x : B) : (term428 B op x) = (term429 B op x).
Proof. exact (MK_COMB (@lem5805748 B op) (@lem5805749 B x)). Qed.
Lemma lem5805751 {B : Type'} (op : type1400 B) (x : B) : (term429 B op x) = (term415 B op x).
Proof. exact (eq_refl (term429 B op x)). Qed.
Lemma lem5805752 {B : Type'} (op : type1400 B) (x : B) : (term428 B op x) = (term415 B op x).
Proof. exact (TRANS (@lem5805750 B op x) (@lem5805751 B op x)). Qed.
Lemma lem5805753 {B : Type'} (op : type1400 B) : (term430 B op) = (term416 B op).
Proof. exact (fun_ext (fun x : B => @lem5805752 B op x)). Qed.
Lemma lem5805754 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805755 {B : Type'} (op : type1400 B) : (term431 B op) = (term417 B op).
Proof. exact (MK_COMB (@lem5805754 B) (@lem5805753 B op)). Qed.
Lemma lem5805756 {B : Type'} : (term432 B) = (term418 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805755 B op)). Qed.
Lemma lem5805757 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805758 {B : Type'} : (term424 B) = (term419 B).
Proof. exact (MK_COMB (@lem5805757 B) (@lem5805756 B)). Qed.
Lemma lem5805759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805760 {B : Type'} : (term433 B) = (term434 B).
Proof. exact (MK_COMB (@lem5805759) (@lem5805758 B)). Qed.
Lemma lem5805761 {B : Type'} (op : type1400 B) : (term427 B op) = (term416 B op).
Proof. exact (eq_refl (term427 B op)). Qed.
Lemma lem5805762 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (x op).
Proof. exact (eq_refl (x op)). Qed.
Lemma lem5805763 {B : Type'} (x : type402 B) (op : type1400 B) : (term435 B x op) = (term436 B x op).
Proof. exact (MK_COMB (@lem5805761 B op) (@lem5805762 B x op)). Qed.
Lemma lem5805764 {B : Type'} (x : type402 B) (op : type1400 B) : (term436 B x op) = (term437 B x op).
Proof. exact (eq_refl (term436 B x op)). Qed.
Lemma lem5805765 {B : Type'} (x : type402 B) (op : type1400 B) : (term435 B x op) = (term437 B x op).
Proof. exact (TRANS (@lem5805763 B x op) (@lem5805764 B x op)). Qed.
Lemma lem5805766 {B : Type'} (x : type402 B) : (term438 B x) = (term439 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805765 B x op)). Qed.
Lemma lem5805767 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805768 {B : Type'} (x : type402 B) : (term440 B x) = (term441 B x).
Proof. exact (MK_COMB (@lem5805767 B) (@lem5805766 B x)). Qed.
Lemma lem5805769 {B : Type'} : (term442 B) = (term443 B).
Proof. exact (fun_ext (fun x : type402 B => @lem5805768 B x)). Qed.
Lemma lem5805770 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805771 {B : Type'} : (term425 B) = (term444 B).
Proof. exact (MK_COMB (@lem5805770 B) (@lem5805769 B)). Qed.
Lemma lem5805772 {B : Type'} : ((term424 B) = (term425 B)) = ((term419 B) = (term444 B)).
Proof. exact (MK_COMB (@lem5805760 B) (@lem5805771 B)). Qed.
Lemma lem5805773 {B : Type'} : (term419 B) = (term444 B).
Proof. exact (EQ_MP (@lem5805772 B) (@lem5805747 B)). Qed.
Lemma lem5805775 {A B : Type'} (P : type1413 A B) : (term420 A B P) = (term421 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5805776 {B : Type'} (P : type401 B) : (term422 B P) = (term423 B P).
Proof. exact (@lem5805775 (type1400 B) B P). Qed.
Lemma lem5805777 {B : Type'} (x : type402 B) : (term445 B x) = (term446 B x).
Proof. exact (@lem5805776 B (term447 B x)). Qed.
Lemma lem5805778 {B : Type'} (x : type402 B) (op : type1400 B) : (term448 B x op) = (term449 B x op).
Proof. exact (eq_refl (term448 B x op)). Qed.
Lemma lem5805779 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5805780 {B : Type'} (x : type402 B) (op : type1400 B) (y : B) : (term450 B x op y) = (term451 B x op y).
Proof. exact (MK_COMB (@lem5805778 B x op) (@lem5805779 B y)). Qed.
Lemma lem5805781 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term451 B x op y) = (term452 B y x op).
Proof. exact (eq_refl (term451 B x op y)). Qed.
Lemma lem5805782 {B : Type'} (y : B) (x : type402 B) (op : type1400 B) : (term450 B x op y) = (term452 B y x op).
Proof. exact (TRANS (@lem5805780 B x op y) (@lem5805781 B y x op)). Qed.
Lemma lem5805783 {B : Type'} (x : type402 B) (op : type1400 B) : (term453 B x op) = (term449 B x op).
Proof. exact (fun_ext (fun y : B => @lem5805782 B y x op)). Qed.
Lemma lem5805784 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805785 {B : Type'} (x : type402 B) (op : type1400 B) : (term454 B x op) = (term437 B x op).
Proof. exact (MK_COMB (@lem5805784 B) (@lem5805783 B x op)). Qed.
Lemma lem5805786 {B : Type'} (x : type402 B) : (term455 B x) = (term439 B x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805785 B x op)). Qed.
Lemma lem5805787 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805788 {B : Type'} (x : type402 B) : (term445 B x) = (term441 B x).
Proof. exact (MK_COMB (@lem5805787 B) (@lem5805786 B x)). Qed.
Lemma lem5805789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805790 {B : Type'} (x : type402 B) : (term456 B x) = (term457 B x).
Proof. exact (MK_COMB (@lem5805789) (@lem5805788 B x)). Qed.
Lemma lem5805791 {B : Type'} (x : type402 B) (op : type1400 B) : (term448 B x op) = (term449 B x op).
Proof. exact (eq_refl (term448 B x op)). Qed.
Lemma lem5805792 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (y op).
Proof. exact (eq_refl (y op)). Qed.
Lemma lem5805793 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term458 B x y op) = (term459 B x y op).
Proof. exact (MK_COMB (@lem5805791 B x op) (@lem5805792 B y op)). Qed.
Lemma lem5805794 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term459 B x y op) = (term460 B y x op).
Proof. exact (eq_refl (term459 B x y op)). Qed.
Lemma lem5805795 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term458 B x y op) = (term460 B y x op).
Proof. exact (TRANS (@lem5805793 B x y op) (@lem5805794 B y x op)). Qed.
Lemma lem5805796 {B : Type'} (y : type402 B) (x : type402 B) : (term461 B x y) = (term462 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805795 B y x op)). Qed.
Lemma lem5805797 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805798 {B : Type'} (y : type402 B) (x : type402 B) : (term463 B x y) = (term464 B y x).
Proof. exact (MK_COMB (@lem5805797 B) (@lem5805796 B y x)). Qed.
Lemma lem5805799 {B : Type'} (x : type402 B) : (term465 B x) = (term466 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem5805798 B y x)). Qed.
Lemma lem5805800 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805801 {B : Type'} (x : type402 B) : (term446 B x) = (term467 B x).
Proof. exact (MK_COMB (@lem5805800 B) (@lem5805799 B x)). Qed.
Lemma lem5805802 {B : Type'} (x : type402 B) : ((term445 B x) = (term446 B x)) = ((term441 B x) = (term467 B x)).
Proof. exact (MK_COMB (@lem5805790 B x) (@lem5805801 B x)). Qed.
Lemma lem5805803 {B : Type'} (x : type402 B) : (term441 B x) = (term467 B x).
Proof. exact (EQ_MP (@lem5805802 B x) (@lem5805777 B x)). Qed.
Lemma lem5805805 {A B : Type'} (P : type1413 A B) : (term420 A B P) = (term421 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5805806 {B : Type'} (P : type401 B) : (term422 B P) = (term423 B P).
Proof. exact (@lem5805805 (type1400 B) B P). Qed.
Lemma lem5805807 {B : Type'} (y : type402 B) (x : type402 B) : (term468 B y x) = (term469 B y x).
Proof. exact (@lem5805806 B (term470 B y x)). Qed.
Lemma lem5805808 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term471 B y x op) = (term472 B y x op).
Proof. exact (eq_refl (term471 B y x op)). Qed.
Lemma lem5805809 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5805810 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) (z : B) : (term473 B y x op z) = (term474 B y x op z).
Proof. exact (MK_COMB (@lem5805808 B y x op) (@lem5805809 B z)). Qed.
Lemma lem5805811 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term474 B y x op z) = (term475 B y z x op).
Proof. exact (eq_refl (term474 B y x op z)). Qed.
Lemma lem5805812 {B : Type'} (y : type402 B) (z : B) (x : type402 B) (op : type1400 B) : (term473 B y x op z) = (term475 B y z x op).
Proof. exact (TRANS (@lem5805810 B y x op z) (@lem5805811 B y z x op)). Qed.
Lemma lem5805813 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term476 B y x op) = (term472 B y x op).
Proof. exact (fun_ext (fun z : B => @lem5805812 B y z x op)). Qed.
Lemma lem5805814 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5805815 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term477 B y x op) = (term460 B y x op).
Proof. exact (MK_COMB (@lem5805814 B) (@lem5805813 B y x op)). Qed.
Lemma lem5805816 {B : Type'} (y : type402 B) (x : type402 B) : (term478 B y x) = (term462 B y x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805815 B y x op)). Qed.
Lemma lem5805817 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805818 {B : Type'} (y : type402 B) (x : type402 B) : (term468 B y x) = (term464 B y x).
Proof. exact (MK_COMB (@lem5805817 B) (@lem5805816 B y x)). Qed.
Lemma lem5805819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805820 {B : Type'} (y : type402 B) (x : type402 B) : (term479 B y x) = (term480 B y x).
Proof. exact (MK_COMB (@lem5805819) (@lem5805818 B y x)). Qed.
Lemma lem5805821 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term471 B y x op) = (term472 B y x op).
Proof. exact (eq_refl (term471 B y x op)). Qed.
Lemma lem5805822 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (z op).
Proof. exact (eq_refl (z op)). Qed.
Lemma lem5805823 {B : Type'} (y : type402 B) (x : type402 B) (z : type402 B) (op : type1400 B) : (term481 B y x z op) = (term482 B y x z op).
Proof. exact (MK_COMB (@lem5805821 B y x op) (@lem5805822 B z op)). Qed.
Lemma lem5805824 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term482 B y x z op) = (term483 B y z x op).
Proof. exact (eq_refl (term482 B y x z op)). Qed.
Lemma lem5805825 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term481 B y x z op) = (term483 B y z x op).
Proof. exact (TRANS (@lem5805823 B y x z op) (@lem5805824 B y z x op)). Qed.
Lemma lem5805826 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term484 B y x z) = (term485 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5805825 B y z x op)). Qed.
Lemma lem5805827 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5805828 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term486 B y x z) = (term487 B y z x).
Proof. exact (MK_COMB (@lem5805827 B) (@lem5805826 B y z x)). Qed.
Lemma lem5805829 {B : Type'} (y : type402 B) (x : type402 B) : (term488 B y x) = (term489 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem5805828 B y z x)). Qed.
Lemma lem5805830 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805831 {B : Type'} (y : type402 B) (x : type402 B) : (term469 B y x) = (term490 B y x).
Proof. exact (MK_COMB (@lem5805830 B) (@lem5805829 B y x)). Qed.
Lemma lem5805832 {B : Type'} (y : type402 B) (x : type402 B) : ((term468 B y x) = (term469 B y x)) = ((term464 B y x) = (term490 B y x)).
Proof. exact (MK_COMB (@lem5805820 B y x) (@lem5805831 B y x)). Qed.
Lemma lem5805833 {B : Type'} (y : type402 B) (x : type402 B) : (term464 B y x) = (term490 B y x).
Proof. exact (EQ_MP (@lem5805832 B y x) (@lem5805807 B y x)). Qed.
Lemma lem5805834 {B : Type'} (x : type402 B) : (term466 B x) = (term491 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem5805833 B y x)). Qed.
Lemma lem5805835 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805836 {B : Type'} (x : type402 B) : (term467 B x) = (term492 B x).
Proof. exact (MK_COMB (@lem5805835 B) (@lem5805834 B x)). Qed.
Lemma lem5805837 {B : Type'} (x : type402 B) : (term441 B x) = (term492 B x).
Proof. exact (TRANS (@lem5805803 B x) (@lem5805836 B x)). Qed.
Lemma lem5805838 {B : Type'} : (term443 B) = (term493 B).
Proof. exact (fun_ext (fun x : type402 B => @lem5805837 B x)). Qed.
Lemma lem5805839 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805840 {B : Type'} : (term444 B) = (term494 B).
Proof. exact (MK_COMB (@lem5805839 B) (@lem5805838 B)). Qed.
Lemma lem5805841 {B : Type'} : (term419 B) = (term494 B).
Proof. exact (TRANS (@lem5805773 B) (@lem5805840 B)). Qed.
Lemma lem5805842 {B : Type'} : (term259 B) = (term494 B).
Proof. exact (TRANS (@lem5805743 B) (@lem5805841 B)). Qed.
Lemma lem5805843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805844 {B : Type'} : (term261 B) = (term495 B).
Proof. exact (MK_COMB (@lem5805843) (@lem5805842 B)). Qed.
Lemma lem5805845 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805846 {B : Type'} : (term265 B) = (term496 B).
Proof. exact (MK_COMB (@lem5805844 B) (@lem5805845 B)). Qed.
Lemma lem5805848 {A : Type'} (P : A -> Prop) (Q : Prop) : (term497 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5805849 {B : Type'} (P : type82 B) (Q : Prop) : (term499 B P Q) = (term500 B P Q).
Proof. exact (@lem5805848 (type402 B) P Q). Qed.
Lemma lem5805850 {B : Type'} : (term501 B) = (term502 B).
Proof. exact (@lem5805849 B (term493 B) (term264 B)). Qed.
Lemma lem5805851 {B : Type'} (x : type402 B) : (term503 B x) = (term492 B x).
Proof. exact (eq_refl (term503 B x)). Qed.
Lemma lem5805852 {B : Type'} : (term504 B) = (term493 B).
Proof. exact (fun_ext (fun x : type402 B => @lem5805851 B x)). Qed.
Lemma lem5805853 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805854 {B : Type'} : (term505 B) = (term494 B).
Proof. exact (MK_COMB (@lem5805853 B) (@lem5805852 B)). Qed.
Lemma lem5805855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805856 {B : Type'} : (term506 B) = (term495 B).
Proof. exact (MK_COMB (@lem5805855) (@lem5805854 B)). Qed.
Lemma lem5805857 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805858 {B : Type'} : (term501 B) = (term496 B).
Proof. exact (MK_COMB (@lem5805856 B) (@lem5805857 B)). Qed.
Lemma lem5805859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805860 {B : Type'} : (term507 B) = (term508 B).
Proof. exact (MK_COMB (@lem5805859) (@lem5805858 B)). Qed.
Lemma lem5805861 {B : Type'} (x : type402 B) : (term503 B x) = (term492 B x).
Proof. exact (eq_refl (term503 B x)). Qed.
Lemma lem5805862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805863 {B : Type'} (x : type402 B) : (term509 B x) = (term510 B x).
Proof. exact (MK_COMB (@lem5805862) (@lem5805861 B x)). Qed.
Lemma lem5805864 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805865 {B : Type'} (x : type402 B) : (term511 B x) = (term512 B x).
Proof. exact (MK_COMB (@lem5805863 B x) (@lem5805864 B)). Qed.
Lemma lem5805866 {B : Type'} : (term513 B) = (term514 B).
Proof. exact (fun_ext (fun x : type402 B => @lem5805865 B x)). Qed.
Lemma lem5805867 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805868 {B : Type'} : (term502 B) = (term515 B).
Proof. exact (MK_COMB (@lem5805867 B) (@lem5805866 B)). Qed.
Lemma lem5805869 {B : Type'} : ((term501 B) = (term502 B)) = ((term496 B) = (term515 B)).
Proof. exact (MK_COMB (@lem5805860 B) (@lem5805868 B)). Qed.
Lemma lem5805870 {B : Type'} : (term496 B) = (term515 B).
Proof. exact (EQ_MP (@lem5805869 B) (@lem5805850 B)). Qed.
Lemma lem5805872 {A : Type'} (P : A -> Prop) (Q : Prop) : (term497 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5805873 {B : Type'} (P : type82 B) (Q : Prop) : (term499 B P Q) = (term500 B P Q).
Proof. exact (@lem5805872 (type402 B) P Q). Qed.
Lemma lem5805874 {B : Type'} (x : type402 B) : (term516 B x) = (term517 B x).
Proof. exact (@lem5805873 B (term491 B x) (term264 B)). Qed.
Lemma lem5805875 {B : Type'} (y : type402 B) (x : type402 B) : (term518 B x y) = (term490 B y x).
Proof. exact (eq_refl (term518 B x y)). Qed.
Lemma lem5805876 {B : Type'} (x : type402 B) : (term519 B x) = (term491 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem5805875 B y x)). Qed.
Lemma lem5805877 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805878 {B : Type'} (x : type402 B) : (term520 B x) = (term492 B x).
Proof. exact (MK_COMB (@lem5805877 B) (@lem5805876 B x)). Qed.
Lemma lem5805879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805880 {B : Type'} (x : type402 B) : (term521 B x) = (term510 B x).
Proof. exact (MK_COMB (@lem5805879) (@lem5805878 B x)). Qed.
Lemma lem5805881 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805882 {B : Type'} (x : type402 B) : (term516 B x) = (term512 B x).
Proof. exact (MK_COMB (@lem5805880 B x) (@lem5805881 B)). Qed.
Lemma lem5805883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805884 {B : Type'} (x : type402 B) : (term522 B x) = (term523 B x).
Proof. exact (MK_COMB (@lem5805883) (@lem5805882 B x)). Qed.
Lemma lem5805885 {B : Type'} (y : type402 B) (x : type402 B) : (term518 B x y) = (term490 B y x).
Proof. exact (eq_refl (term518 B x y)). Qed.
Lemma lem5805886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805887 {B : Type'} (y : type402 B) (x : type402 B) : (term524 B x y) = (term525 B y x).
Proof. exact (MK_COMB (@lem5805886) (@lem5805885 B y x)). Qed.
Lemma lem5805888 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805889 {B : Type'} (y : type402 B) (x : type402 B) : (term526 B x y) = (term527 B y x).
Proof. exact (MK_COMB (@lem5805887 B y x) (@lem5805888 B)). Qed.
Lemma lem5805890 {B : Type'} (x : type402 B) : (term528 B x) = (term529 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem5805889 B y x)). Qed.
Lemma lem5805891 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805892 {B : Type'} (x : type402 B) : (term517 B x) = (term530 B x).
Proof. exact (MK_COMB (@lem5805891 B) (@lem5805890 B x)). Qed.
Lemma lem5805893 {B : Type'} (x : type402 B) : ((term516 B x) = (term517 B x)) = ((term512 B x) = (term530 B x)).
Proof. exact (MK_COMB (@lem5805884 B x) (@lem5805892 B x)). Qed.
Lemma lem5805894 {B : Type'} (x : type402 B) : (term512 B x) = (term530 B x).
Proof. exact (EQ_MP (@lem5805893 B x) (@lem5805874 B x)). Qed.
Lemma lem5805896 {A : Type'} (P : A -> Prop) (Q : Prop) : (term497 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5805897 {B : Type'} (P : type82 B) (Q : Prop) : (term499 B P Q) = (term500 B P Q).
Proof. exact (@lem5805896 (type402 B) P Q). Qed.
Lemma lem5805898 {B : Type'} (y : type402 B) (x : type402 B) : (term531 B y x) = (term532 B y x).
Proof. exact (@lem5805897 B (term489 B y x) (term264 B)). Qed.
Lemma lem5805899 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term533 B y x z) = (term487 B y z x).
Proof. exact (eq_refl (term533 B y x z)). Qed.
Lemma lem5805900 {B : Type'} (y : type402 B) (x : type402 B) : (term534 B y x) = (term489 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem5805899 B y z x)). Qed.
Lemma lem5805901 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805902 {B : Type'} (y : type402 B) (x : type402 B) : (term535 B y x) = (term490 B y x).
Proof. exact (MK_COMB (@lem5805901 B) (@lem5805900 B y x)). Qed.
Lemma lem5805903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805904 {B : Type'} (y : type402 B) (x : type402 B) : (term536 B y x) = (term525 B y x).
Proof. exact (MK_COMB (@lem5805903) (@lem5805902 B y x)). Qed.
Lemma lem5805905 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805906 {B : Type'} (y : type402 B) (x : type402 B) : (term531 B y x) = (term527 B y x).
Proof. exact (MK_COMB (@lem5805904 B y x) (@lem5805905 B)). Qed.
Lemma lem5805907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5805908 {B : Type'} (y : type402 B) (x : type402 B) : (term537 B y x) = (term538 B y x).
Proof. exact (MK_COMB (@lem5805907) (@lem5805906 B y x)). Qed.
Lemma lem5805909 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term533 B y x z) = (term487 B y z x).
Proof. exact (eq_refl (term533 B y x z)). Qed.
Lemma lem5805910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5805911 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term539 B y x z) = (term540 B y z x).
Proof. exact (MK_COMB (@lem5805910) (@lem5805909 B y z x)). Qed.
Lemma lem5805912 {B : Type'} : (term264 B) = (term264 B).
Proof. exact (eq_refl (term264 B)). Qed.
Lemma lem5805913 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term541 B y x z) = (term542 B y z x).
Proof. exact (MK_COMB (@lem5805911 B y z x) (@lem5805912 B)). Qed.
Lemma lem5805914 {B : Type'} (y : type402 B) (x : type402 B) : (term543 B y x) = (term544 B y x).
Proof. exact (fun_ext (fun z : type402 B => @lem5805913 B y z x)). Qed.
Lemma lem5805915 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805916 {B : Type'} (y : type402 B) (x : type402 B) : (term532 B y x) = (term545 B y x).
Proof. exact (MK_COMB (@lem5805915 B) (@lem5805914 B y x)). Qed.
Lemma lem5805917 {B : Type'} (y : type402 B) (x : type402 B) : ((term531 B y x) = (term532 B y x)) = ((term527 B y x) = (term545 B y x)).
Proof. exact (MK_COMB (@lem5805908 B y x) (@lem5805916 B y x)). Qed.
Lemma lem5805918 {B : Type'} (y : type402 B) (x : type402 B) : (term527 B y x) = (term545 B y x).
Proof. exact (EQ_MP (@lem5805917 B y x) (@lem5805898 B y x)). Qed.
Lemma lem5805919 {B : Type'} (x : type402 B) : (term529 B x) = (term546 B x).
Proof. exact (fun_ext (fun y : type402 B => @lem5805918 B y x)). Qed.
Lemma lem5805920 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805921 {B : Type'} (x : type402 B) : (term530 B x) = (term547 B x).
Proof. exact (MK_COMB (@lem5805920 B) (@lem5805919 B x)). Qed.
Lemma lem5805922 {B : Type'} (x : type402 B) : (term512 B x) = (term547 B x).
Proof. exact (TRANS (@lem5805894 B x) (@lem5805921 B x)). Qed.
Lemma lem5805923 {B : Type'} : (term514 B) = (term548 B).
Proof. exact (fun_ext (fun x : type402 B => @lem5805922 B x)). Qed.
Lemma lem5805924 {B : Type'} : (@ex ((B -> B -> B) -> B)) = (@ex ((B -> B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B -> B) -> B))). Qed.
Lemma lem5805925 {B : Type'} : (term515 B) = (term549 B).
Proof. exact (MK_COMB (@lem5805924 B) (@lem5805923 B)). Qed.
Lemma lem5805926 {B : Type'} : (term496 B) = (term549 B).
Proof. exact (TRANS (@lem5805870 B) (@lem5805925 B)). Qed.
Lemma lem5805927 {B : Type'} : (term265 B) = (term549 B).
Proof. exact (TRANS (@lem5805846 B) (@lem5805926 B)). Qed.
Lemma lem5805928 {B : Type'} : (term241 B) = (term549 B).
Proof. exact (TRANS (@lem5805377 B) (@lem5805927 B)). Qed.
Lemma lem5805929 {B : Type'} : (term82 B) = (term549 B).
Proof. exact (TRANS (@lem5805350 B) (@lem5805928 B)). Qed.
Lemma lem5805930 {B : Type'} (h1 : term82 B) : term549 B.
Proof. exact (EQ_MP (@lem5805929 B) (@lem5805110 B h1)). Qed.
Lemma lem5805931 {B : Type'} (x : type402 B) (h1 : term547 B x) : term547 B x.
Proof. exact (h1). Qed.
Lemma lem5805932 {B : Type'} (y : type402 B) (x : type402 B) (h1 : term545 B y x) : term545 B y x.
Proof. exact (h1). Qed.
Lemma lem5805933 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term542 B y z x.
Proof. exact (h1). Qed.
Lemma lem5805934 {A B : Type'} (op : type1400 B) (h1 : term173 A B op) : term173 A B op.
Proof. exact (h1). Qed.
Lemma lem5805935 {A B : Type'} (op : type1400 B) (f : A -> B) (h1 : term171 A B op f) : term171 A B op f.
Proof. exact (h1). Qed.
Lemma lem5805936 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term168 A B op f x'.
Proof. exact (h1). Qed.
Lemma lem5805937 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5805938 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5805943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805944 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5805943 (type1400 B) B f x). Qed.
Lemma lem5805946 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5805944 B (@neutral B) op). Qed.
Lemma lem5805947 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5805948 {B : Type'} (op : type1400 B) : (term550 B op) = (term551 B op).
Proof. exact (MK_COMB (@lem5805938 B op) (@lem5805946 B op)). Qed.
Lemma lem5805949 {B : Type'} (op : type1400 B) (x : B) : (term91 B op x) = (term552 B op x).
Proof. exact (MK_COMB (@lem5805948 B op) (@lem5805947 B x)). Qed.
Lemma lem5805951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805952 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5805951 B (B -> B) f x). Qed.
Lemma lem5805953 {B : Type'} (op : type1400 B) : (term551 B op) = (term553 B op).
Proof. exact (@lem5805952 B op (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem5805954 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5805955 {B : Type'} (op : type1400 B) (x : B) : (term552 B op x) = (term554 B op x).
Proof. exact (MK_COMB (@lem5805953 B op) (@lem5805954 B x)). Qed.
Lemma lem5805957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805958 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5805957 B B f x). Qed.
Lemma lem5805959 {B : Type'} (op : type1400 B) (x : B) : (term554 B op x) = (term555 B op x).
Proof. exact (@lem5805958 B (term553 B op) x). Qed.
Lemma lem5805960 {B : Type'} (op : type1400 B) (x : B) : (term552 B op x) = (term555 B op x).
Proof. exact (TRANS (@lem5805955 B op x) (@lem5805959 B op x)). Qed.
Lemma lem5805961 {B : Type'} (op : type1400 B) (x : B) : (term91 B op x) = (term555 B op x).
Proof. exact (TRANS (@lem5805949 B op x) (@lem5805960 B op x)). Qed.
Lemma lem5805962 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5805963 {B : Type'} (op : type1400 B) (x : B) : (term556 B op x) = (term557 B op x).
Proof. exact (MK_COMB (@lem5805937 B) (@lem5805961 B op x)). Qed.
Lemma lem5805964 {B : Type'} (op : type1400 B) (x : B) : ((term91 B op x) = x) = ((term555 B op x) = x).
Proof. exact (MK_COMB (@lem5805963 B op x) (@lem5805962 B x)). Qed.
Lemma lem5805965 {B : Type'} (op : type1400 B) : (term92 B op) = (term558 B op).
Proof. exact (fun_ext (fun x : B => @lem5805964 B op x)). Qed.
Lemma lem5805966 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5805967 {B : Type'} (op : type1400 B) : (term93 B op) = (term559 B op).
Proof. exact (MK_COMB (@lem5805966 B) (@lem5805965 B op)). Qed.
Lemma lem5805968 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5805977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805978 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5805977 B (B -> B) f x). Qed.
Lemma lem5805979 {B : Type'} (op : type1400 B) (y : B) : (op y) = (@I (B -> B -> B) op y).
Proof. exact (@lem5805978 B op y). Qed.
Lemma lem5805980 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5805981 {B : Type'} (op : type1400 B) (y : B) (z : B) : (op y z) = (@I (B -> B -> B) op y z).
Proof. exact (MK_COMB (@lem5805979 B op y) (@lem5805980 B z)). Qed.
Lemma lem5805983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805984 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5805983 B B f x). Qed.
Lemma lem5805985 {B : Type'} (op : type1400 B) (y : B) (z : B) : (@I (B -> B -> B) op y z) = (term560 B op y z).
Proof. exact (@lem5805984 B (@I (B -> B -> B) op y) z). Qed.
Lemma lem5805987 {B : Type'} (op : type1400 B) (y : B) (z : B) : (op y z) = (term560 B op y z).
Proof. exact (TRANS (@lem5805981 B op y z) (@lem5805985 B op y z)). Qed.
Lemma lem5805988 {B : Type'} (op : type1400 B) (x : B) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem5805989 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term94 B x op y z) = (term561 B x op y z).
Proof. exact (MK_COMB (@lem5805988 B op x) (@lem5805987 B op y z)). Qed.
Lemma lem5805991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805992 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5805991 B (B -> B) f x). Qed.
Lemma lem5805993 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem5805992 B op x). Qed.
Lemma lem5805994 {B : Type'} (op : type1400 B) (y : B) (z : B) : (term560 B op y z) = (term560 B op y z).
Proof. exact (eq_refl (term560 B op y z)). Qed.
Lemma lem5805995 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term561 B x op y z) = (term562 B x op y z).
Proof. exact (MK_COMB (@lem5805993 B op x) (@lem5805994 B op y z)). Qed.
Lemma lem5805997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5805998 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5805997 B B f x). Qed.
Lemma lem5805999 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term562 B x op y z) = (term563 B x op y z).
Proof. exact (@lem5805998 B (@I (B -> B -> B) op x) (term560 B op y z)). Qed.
Lemma lem5806000 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term561 B x op y z) = (term563 B x op y z).
Proof. exact (TRANS (@lem5805995 B x op y z) (@lem5805999 B x op y z)). Qed.
Lemma lem5806001 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term94 B x op y z) = (term563 B x op y z).
Proof. exact (TRANS (@lem5805989 B x op y z) (@lem5806000 B x op y z)). Qed.
Lemma lem5806002 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806010 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806009 B (B -> B) f x). Qed.
Lemma lem5806011 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem5806010 B op x). Qed.
Lemma lem5806012 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5806013 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (@I (B -> B -> B) op x y).
Proof. exact (MK_COMB (@lem5806011 B op x) (@lem5806012 B y)). Qed.
Lemma lem5806015 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806016 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806015 B B f x). Qed.
Lemma lem5806017 {B : Type'} (op : type1400 B) (x : B) (y : B) : (@I (B -> B -> B) op x y) = (term560 B op x y).
Proof. exact (@lem5806016 B (@I (B -> B -> B) op x) y). Qed.
Lemma lem5806019 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (term560 B op x y).
Proof. exact (TRANS (@lem5806013 B op x y) (@lem5806017 B op x y)). Qed.
Lemma lem5806020 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5806021 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term564 B op x y) = (term565 B op x y).
Proof. exact (MK_COMB (@lem5806002 B op) (@lem5806019 B op x y)). Qed.
Lemma lem5806022 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term95 B op x y z) = (term566 B op x y z).
Proof. exact (MK_COMB (@lem5806021 B op x y) (@lem5806020 B z)). Qed.
Lemma lem5806024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806025 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806024 B (B -> B) f x). Qed.
Lemma lem5806026 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term565 B op x y) = (term567 B op x y).
Proof. exact (@lem5806025 B op (term560 B op x y)). Qed.
Lemma lem5806027 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5806028 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term566 B op x y z) = (term568 B op x y z).
Proof. exact (MK_COMB (@lem5806026 B op x y) (@lem5806027 B z)). Qed.
Lemma lem5806030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806031 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806030 B B f x). Qed.
Lemma lem5806032 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term568 B op x y z) = (term569 B op x y z).
Proof. exact (@lem5806031 B (term567 B op x y) z). Qed.
Lemma lem5806033 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term566 B op x y z) = (term569 B op x y z).
Proof. exact (TRANS (@lem5806028 B op x y z) (@lem5806032 B op x y z)). Qed.
Lemma lem5806034 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term95 B op x y z) = (term569 B op x y z).
Proof. exact (TRANS (@lem5806022 B op x y z) (@lem5806033 B op x y z)). Qed.
Lemma lem5806035 {B : Type'} (x : B) (op : type1400 B) (y : B) (z : B) : (term570 B x op y z) = (term571 B x op y z).
Proof. exact (MK_COMB (@lem5805968 B) (@lem5806001 B x op y z)). Qed.
Lemma lem5806036 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : ((term94 B x op y z) = (term95 B op x y z)) = ((term563 B x op y z) = (term569 B op x y z)).
Proof. exact (MK_COMB (@lem5806035 B x op y z) (@lem5806034 B op x y z)). Qed.
Lemma lem5806037 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term96 B op x y) = (term572 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5806036 B op x y z)). Qed.
Lemma lem5806038 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806039 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term97 B op x y) = (term573 B op x y).
Proof. exact (MK_COMB (@lem5806038 B) (@lem5806037 B op x y)). Qed.
Lemma lem5806040 {B : Type'} (op : type1400 B) (x : B) : (term98 B op x) = (term574 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806039 B op x y)). Qed.
Lemma lem5806041 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806042 {B : Type'} (op : type1400 B) (x : B) : (term99 B op x) = (term575 B op x).
Proof. exact (MK_COMB (@lem5806041 B) (@lem5806040 B op x)). Qed.
Lemma lem5806043 {B : Type'} (op : type1400 B) : (term100 B op) = (term576 B op).
Proof. exact (fun_ext (fun x : B => @lem5806042 B op x)). Qed.
Lemma lem5806044 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806045 {B : Type'} (op : type1400 B) : (term101 B op) = (term577 B op).
Proof. exact (MK_COMB (@lem5806044 B) (@lem5806043 B op)). Qed.
Lemma lem5806046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806047 {B : Type'} (op : type1400 B) : (term102 B op) = (term578 B op).
Proof. exact (MK_COMB (@lem5806046) (@lem5806045 B op)). Qed.
Lemma lem5806048 {B : Type'} (op : type1400 B) : (term103 B op) = (term579 B op).
Proof. exact (MK_COMB (@lem5806047 B op) (@lem5805967 B op)). Qed.
Lemma lem5806049 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5806056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806057 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806056 B (B -> B) f x). Qed.
Lemma lem5806058 {B : Type'} (op : type1400 B) (x : B) : (op x) = (@I (B -> B -> B) op x).
Proof. exact (@lem5806057 B op x). Qed.
Lemma lem5806059 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5806060 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (@I (B -> B -> B) op x y).
Proof. exact (MK_COMB (@lem5806058 B op x) (@lem5806059 B y)). Qed.
Lemma lem5806062 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806063 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806062 B B f x). Qed.
Lemma lem5806064 {B : Type'} (op : type1400 B) (x : B) (y : B) : (@I (B -> B -> B) op x y) = (term560 B op x y).
Proof. exact (@lem5806063 B (@I (B -> B -> B) op x) y). Qed.
Lemma lem5806066 {B : Type'} (op : type1400 B) (x : B) (y : B) : (op x y) = (term560 B op x y).
Proof. exact (TRANS (@lem5806060 B op x y) (@lem5806064 B op x y)). Qed.
Lemma lem5806073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806074 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806073 B (B -> B) f x). Qed.
Lemma lem5806075 {B : Type'} (op : type1400 B) (y : B) : (op y) = (@I (B -> B -> B) op y).
Proof. exact (@lem5806074 B op y). Qed.
Lemma lem5806076 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5806077 {B : Type'} (op : type1400 B) (y : B) (x : B) : (op y x) = (@I (B -> B -> B) op y x).
Proof. exact (MK_COMB (@lem5806075 B op y) (@lem5806076 B x)). Qed.
Lemma lem5806079 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806080 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806079 B B f x). Qed.
Lemma lem5806081 {B : Type'} (op : type1400 B) (y : B) (x : B) : (@I (B -> B -> B) op y x) = (term560 B op y x).
Proof. exact (@lem5806080 B (@I (B -> B -> B) op y) x). Qed.
Lemma lem5806083 {B : Type'} (op : type1400 B) (y : B) (x : B) : (op y x) = (term560 B op y x).
Proof. exact (TRANS (@lem5806077 B op y x) (@lem5806081 B op y x)). Qed.
Lemma lem5806084 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term580 B op x y) = (term581 B op x y).
Proof. exact (MK_COMB (@lem5806049 B) (@lem5806066 B op x y)). Qed.
Lemma lem5806085 {B : Type'} (op : type1400 B) (y : B) (x : B) : ((op x y) = (op y x)) = ((term560 B op x y) = (term560 B op y x)).
Proof. exact (MK_COMB (@lem5806084 B op x y) (@lem5806083 B op y x)). Qed.
Lemma lem5806086 {B : Type'} (op : type1400 B) (x : B) : (term104 B op x) = (term582 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806085 B op y x)). Qed.
Lemma lem5806087 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806088 {B : Type'} (op : type1400 B) (x : B) : (term105 B op x) = (term583 B op x).
Proof. exact (MK_COMB (@lem5806087 B) (@lem5806086 B op x)). Qed.
Lemma lem5806089 {B : Type'} (op : type1400 B) : (term106 B op) = (term584 B op).
Proof. exact (fun_ext (fun x : B => @lem5806088 B op x)). Qed.
Lemma lem5806090 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806091 {B : Type'} (op : type1400 B) : (term107 B op) = (term585 B op).
Proof. exact (MK_COMB (@lem5806090 B) (@lem5806089 B op)). Qed.
Lemma lem5806092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806093 {B : Type'} (op : type1400 B) : (term108 B op) = (term586 B op).
Proof. exact (MK_COMB (@lem5806092) (@lem5806091 B op)). Qed.
Lemma lem5806094 {B : Type'} (op : type1400 B) : (term109 B op) = (term587 B op).
Proof. exact (MK_COMB (@lem5806093 B op) (@lem5806048 B op)). Qed.
Lemma lem5806095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5806100 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806101 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5806100 (type1400 B) Prop f x). Qed.
Lemma lem5806103 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5806101 B (@monoidal B) op). Qed.
Lemma lem5806104 {B : Type'} (op : type1400 B) : (term588 B op) = (term589 B op).
Proof. exact (MK_COMB (@lem5806095) (@lem5806103 B op)). Qed.
Lemma lem5806105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5806106 {B : Type'} (op : type1400 B) : (term231 B op) = (term590 B op).
Proof. exact (MK_COMB (@lem5806105) (@lem5806104 B op)). Qed.
Lemma lem5806107 {B : Type'} (op : type1400 B) : (term232 B op) = (term591 B op).
Proof. exact (MK_COMB (@lem5806106 B op) (@lem5806094 B op)). Qed.
Lemma lem5806108 {B : Type'} : (term249 B) = (term592 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5806107 B op)). Qed.
Lemma lem5806109 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5806110 {B : Type'} : (term264 B) = (term593 B).
Proof. exact (MK_COMB (@lem5806109 B) (@lem5806108 B)). Qed.
Lemma lem5806111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5806112 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5806113 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806119 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806118 (type1400 B) B f x). Qed.
Lemma lem5806121 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5806119 B (@neutral B) op). Qed.
Lemma lem5806126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806127 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806126 (type1400 B) B f x). Qed.
Lemma lem5806129 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806127 B x op). Qed.
Lemma lem5806130 {B : Type'} (op : type1400 B) : (term550 B op) = (term551 B op).
Proof. exact (MK_COMB (@lem5806113 B op) (@lem5806121 B op)). Qed.
Lemma lem5806131 {B : Type'} (x : type402 B) (op : type1400 B) : (term594 B x op) = (term595 B x op).
Proof. exact (MK_COMB (@lem5806130 B op) (@lem5806129 B x op)). Qed.
Lemma lem5806133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806134 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806133 B (B -> B) f x). Qed.
Lemma lem5806135 {B : Type'} (op : type1400 B) : (term551 B op) = (term553 B op).
Proof. exact (@lem5806134 B op (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem5806136 {B : Type'} (x : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806137 {B : Type'} (x : type402 B) (op : type1400 B) : (term595 B x op) = (term596 B x op).
Proof. exact (MK_COMB (@lem5806135 B op) (@lem5806136 B x op)). Qed.
Lemma lem5806139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806140 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806139 B B f x). Qed.
Lemma lem5806141 {B : Type'} (x : type402 B) (op : type1400 B) : (term596 B x op) = (term597 B x op).
Proof. exact (@lem5806140 B (term553 B op) (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806142 {B : Type'} (x : type402 B) (op : type1400 B) : (term595 B x op) = (term597 B x op).
Proof. exact (TRANS (@lem5806137 B x op) (@lem5806141 B x op)). Qed.
Lemma lem5806143 {B : Type'} (x : type402 B) (op : type1400 B) : (term594 B x op) = (term597 B x op).
Proof. exact (TRANS (@lem5806131 B x op) (@lem5806142 B x op)). Qed.
Lemma lem5806148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806149 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806148 (type1400 B) B f x). Qed.
Lemma lem5806151 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806149 B x op). Qed.
Lemma lem5806152 {B : Type'} (x : type402 B) (op : type1400 B) : (term598 B x op) = (term599 B x op).
Proof. exact (MK_COMB (@lem5806112 B) (@lem5806143 B x op)). Qed.
Lemma lem5806153 {B : Type'} (x : type402 B) (op : type1400 B) : ((term594 B x op) = (x op)) = ((term597 B x op) = (@I ((B -> B -> B) -> B) x op)).
Proof. exact (MK_COMB (@lem5806152 B x op) (@lem5806151 B x op)). Qed.
Lemma lem5806154 {B : Type'} (x : type402 B) (op : type1400 B) : (term600 B x op) = (term601 B x op).
Proof. exact (MK_COMB (@lem5806111) (@lem5806153 B x op)). Qed.
Lemma lem5806155 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5806156 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5806157 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806163 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806162 (type1400 B) B f x). Qed.
Lemma lem5806165 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806163 B x op). Qed.
Lemma lem5806166 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806172 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806171 (type1400 B) B f x). Qed.
Lemma lem5806174 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem5806172 B y op). Qed.
Lemma lem5806179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806180 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806179 (type1400 B) B f x). Qed.
Lemma lem5806182 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (@lem5806180 B z op). Qed.
Lemma lem5806183 {B : Type'} (y : type402 B) (op : type1400 B) : (term602 B y op) = (term603 B y op).
Proof. exact (MK_COMB (@lem5806166 B op) (@lem5806174 B y op)). Qed.
Lemma lem5806184 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term604 B y z op) = (term605 B y z op).
Proof. exact (MK_COMB (@lem5806183 B y op) (@lem5806182 B z op)). Qed.
Lemma lem5806186 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806187 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806186 B (B -> B) f x). Qed.
Lemma lem5806188 {B : Type'} (y : type402 B) (op : type1400 B) : (term603 B y op) = (term606 B y op).
Proof. exact (@lem5806187 B op (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806189 {B : Type'} (z : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem5806190 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term605 B y z op) = (term607 B y z op).
Proof. exact (MK_COMB (@lem5806188 B y op) (@lem5806189 B z op)). Qed.
Lemma lem5806192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806193 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806192 B B f x). Qed.
Lemma lem5806194 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term607 B y z op) = (term608 B y z op).
Proof. exact (@lem5806193 B (term606 B y op) (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem5806195 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term605 B y z op) = (term608 B y z op).
Proof. exact (TRANS (@lem5806190 B y z op) (@lem5806194 B y z op)). Qed.
Lemma lem5806196 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term604 B y z op) = (term608 B y z op).
Proof. exact (TRANS (@lem5806184 B y z op) (@lem5806195 B y z op)). Qed.
Lemma lem5806197 {B : Type'} (x : type402 B) (op : type1400 B) : (term602 B x op) = (term603 B x op).
Proof. exact (MK_COMB (@lem5806157 B op) (@lem5806165 B x op)). Qed.
Lemma lem5806198 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term609 B x y z op) = (term610 B x y z op).
Proof. exact (MK_COMB (@lem5806197 B x op) (@lem5806196 B y z op)). Qed.
Lemma lem5806200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806201 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806200 B (B -> B) f x). Qed.
Lemma lem5806202 {B : Type'} (x : type402 B) (op : type1400 B) : (term603 B x op) = (term606 B x op).
Proof. exact (@lem5806201 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806203 {B : Type'} (y : type402 B) (z : type402 B) (op : type1400 B) : (term608 B y z op) = (term608 B y z op).
Proof. exact (eq_refl (term608 B y z op)). Qed.
Lemma lem5806204 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term610 B x y z op) = (term611 B x y z op).
Proof. exact (MK_COMB (@lem5806202 B x op) (@lem5806203 B y z op)). Qed.
Lemma lem5806206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806207 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806206 B B f x). Qed.
Lemma lem5806208 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term611 B x y z op) = (term612 B x y z op).
Proof. exact (@lem5806207 B (term606 B x op) (term608 B y z op)). Qed.
Lemma lem5806209 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term610 B x y z op) = (term612 B x y z op).
Proof. exact (TRANS (@lem5806204 B x y z op) (@lem5806208 B x y z op)). Qed.
Lemma lem5806210 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term609 B x y z op) = (term612 B x y z op).
Proof. exact (TRANS (@lem5806198 B x y z op) (@lem5806209 B x y z op)). Qed.
Lemma lem5806211 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806212 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806218 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806217 (type1400 B) B f x). Qed.
Lemma lem5806220 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806218 B x op). Qed.
Lemma lem5806225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806226 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806225 (type1400 B) B f x). Qed.
Lemma lem5806228 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem5806226 B y op). Qed.
Lemma lem5806229 {B : Type'} (x : type402 B) (op : type1400 B) : (term602 B x op) = (term603 B x op).
Proof. exact (MK_COMB (@lem5806212 B op) (@lem5806220 B x op)). Qed.
Lemma lem5806230 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term604 B x y op) = (term605 B x y op).
Proof. exact (MK_COMB (@lem5806229 B x op) (@lem5806228 B y op)). Qed.
Lemma lem5806232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806233 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806232 B (B -> B) f x). Qed.
Lemma lem5806234 {B : Type'} (x : type402 B) (op : type1400 B) : (term603 B x op) = (term606 B x op).
Proof. exact (@lem5806233 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806235 {B : Type'} (y : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806236 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term605 B x y op) = (term607 B x y op).
Proof. exact (MK_COMB (@lem5806234 B x op) (@lem5806235 B y op)). Qed.
Lemma lem5806238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806239 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806238 B B f x). Qed.
Lemma lem5806240 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term607 B x y op) = (term608 B x y op).
Proof. exact (@lem5806239 B (term606 B x op) (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806241 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term605 B x y op) = (term608 B x y op).
Proof. exact (TRANS (@lem5806236 B x y op) (@lem5806240 B x y op)). Qed.
Lemma lem5806242 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term604 B x y op) = (term608 B x y op).
Proof. exact (TRANS (@lem5806230 B x y op) (@lem5806241 B x y op)). Qed.
Lemma lem5806247 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806248 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806247 (type1400 B) B f x). Qed.
Lemma lem5806250 {B : Type'} (z : type402 B) (op : type1400 B) : (z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (@lem5806248 B z op). Qed.
Lemma lem5806251 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term613 B x y op) = (term614 B x y op).
Proof. exact (MK_COMB (@lem5806211 B op) (@lem5806242 B x y op)). Qed.
Lemma lem5806252 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term615 B x y z op) = (term616 B x y z op).
Proof. exact (MK_COMB (@lem5806251 B x y op) (@lem5806250 B z op)). Qed.
Lemma lem5806254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806255 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806254 B (B -> B) f x). Qed.
Lemma lem5806256 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term614 B x y op) = (term617 B x y op).
Proof. exact (@lem5806255 B op (term608 B x y op)). Qed.
Lemma lem5806257 {B : Type'} (z : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) z op) = (@I ((B -> B -> B) -> B) z op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem5806258 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term616 B x y z op) = (term618 B x y z op).
Proof. exact (MK_COMB (@lem5806256 B x y op) (@lem5806257 B z op)). Qed.
Lemma lem5806260 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806261 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806260 B B f x). Qed.
Lemma lem5806262 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term618 B x y z op) = (term619 B x y z op).
Proof. exact (@lem5806261 B (term617 B x y op) (@I ((B -> B -> B) -> B) z op)). Qed.
Lemma lem5806263 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term616 B x y z op) = (term619 B x y z op).
Proof. exact (TRANS (@lem5806258 B x y z op) (@lem5806262 B x y z op)). Qed.
Lemma lem5806264 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term615 B x y z op) = (term619 B x y z op).
Proof. exact (TRANS (@lem5806252 B x y z op) (@lem5806263 B x y z op)). Qed.
Lemma lem5806265 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term620 B x y z op) = (term621 B x y z op).
Proof. exact (MK_COMB (@lem5806156 B) (@lem5806210 B x y z op)). Qed.
Lemma lem5806266 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : ((term609 B x y z op) = (term615 B x y z op)) = ((term612 B x y z op) = (term619 B x y z op)).
Proof. exact (MK_COMB (@lem5806265 B x y z op) (@lem5806264 B x y z op)). Qed.
Lemma lem5806267 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term622 B x y z op) = (term623 B x y z op).
Proof. exact (MK_COMB (@lem5806155) (@lem5806266 B x y z op)). Qed.
Lemma lem5806268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5806269 {B : Type'} (x : type402 B) (y : type402 B) (z : type402 B) (op : type1400 B) : (term624 B x y z op) = (term625 B x y z op).
Proof. exact (MK_COMB (@lem5806268) (@lem5806267 B x y z op)). Qed.
Lemma lem5806270 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term626 B y z x op) = (term627 B y z x op).
Proof. exact (MK_COMB (@lem5806269 B x y z op) (@lem5806154 B x op)). Qed.
Lemma lem5806271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5806272 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5806273 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806279 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806278 (type1400 B) B f x). Qed.
Lemma lem5806281 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806279 B x op). Qed.
Lemma lem5806286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806287 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806286 (type1400 B) B f x). Qed.
Lemma lem5806289 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem5806287 B y op). Qed.
Lemma lem5806290 {B : Type'} (x : type402 B) (op : type1400 B) : (term602 B x op) = (term603 B x op).
Proof. exact (MK_COMB (@lem5806273 B op) (@lem5806281 B x op)). Qed.
Lemma lem5806291 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term604 B x y op) = (term605 B x y op).
Proof. exact (MK_COMB (@lem5806290 B x op) (@lem5806289 B y op)). Qed.
Lemma lem5806293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806294 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806293 B (B -> B) f x). Qed.
Lemma lem5806295 {B : Type'} (x : type402 B) (op : type1400 B) : (term603 B x op) = (term606 B x op).
Proof. exact (@lem5806294 B op (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806296 {B : Type'} (y : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806297 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term605 B x y op) = (term607 B x y op).
Proof. exact (MK_COMB (@lem5806295 B x op) (@lem5806296 B y op)). Qed.
Lemma lem5806299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806300 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806299 B B f x). Qed.
Lemma lem5806301 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term607 B x y op) = (term608 B x y op).
Proof. exact (@lem5806300 B (term606 B x op) (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806302 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term605 B x y op) = (term608 B x y op).
Proof. exact (TRANS (@lem5806297 B x y op) (@lem5806301 B x y op)). Qed.
Lemma lem5806303 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term604 B x y op) = (term608 B x y op).
Proof. exact (TRANS (@lem5806291 B x y op) (@lem5806302 B x y op)). Qed.
Lemma lem5806304 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806310 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806309 (type1400 B) B f x). Qed.
Lemma lem5806312 {B : Type'} (y : type402 B) (op : type1400 B) : (y op) = (@I ((B -> B -> B) -> B) y op).
Proof. exact (@lem5806310 B y op). Qed.
Lemma lem5806317 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806318 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806317 (type1400 B) B f x). Qed.
Lemma lem5806320 {B : Type'} (x : type402 B) (op : type1400 B) : (x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (@lem5806318 B x op). Qed.
Lemma lem5806321 {B : Type'} (y : type402 B) (op : type1400 B) : (term602 B y op) = (term603 B y op).
Proof. exact (MK_COMB (@lem5806304 B op) (@lem5806312 B y op)). Qed.
Lemma lem5806322 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term604 B y x op) = (term605 B y x op).
Proof. exact (MK_COMB (@lem5806321 B y op) (@lem5806320 B x op)). Qed.
Lemma lem5806324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806325 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806324 B (B -> B) f x). Qed.
Lemma lem5806326 {B : Type'} (y : type402 B) (op : type1400 B) : (term603 B y op) = (term606 B y op).
Proof. exact (@lem5806325 B op (@I ((B -> B -> B) -> B) y op)). Qed.
Lemma lem5806327 {B : Type'} (x : type402 B) (op : type1400 B) : (@I ((B -> B -> B) -> B) x op) = (@I ((B -> B -> B) -> B) x op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806328 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term605 B y x op) = (term607 B y x op).
Proof. exact (MK_COMB (@lem5806326 B y op) (@lem5806327 B x op)). Qed.
Lemma lem5806330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806331 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806330 B B f x). Qed.
Lemma lem5806332 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term607 B y x op) = (term608 B y x op).
Proof. exact (@lem5806331 B (term606 B y op) (@I ((B -> B -> B) -> B) x op)). Qed.
Lemma lem5806333 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term605 B y x op) = (term608 B y x op).
Proof. exact (TRANS (@lem5806328 B y x op) (@lem5806332 B y x op)). Qed.
Lemma lem5806334 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term604 B y x op) = (term608 B y x op).
Proof. exact (TRANS (@lem5806322 B y x op) (@lem5806333 B y x op)). Qed.
Lemma lem5806335 {B : Type'} (x : type402 B) (y : type402 B) (op : type1400 B) : (term628 B x y op) = (term629 B x y op).
Proof. exact (MK_COMB (@lem5806272 B) (@lem5806303 B x y op)). Qed.
Lemma lem5806336 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : ((term604 B x y op) = (term604 B y x op)) = ((term608 B x y op) = (term608 B y x op)).
Proof. exact (MK_COMB (@lem5806335 B x y op) (@lem5806334 B y x op)). Qed.
Lemma lem5806337 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term630 B y x op) = (term631 B y x op).
Proof. exact (MK_COMB (@lem5806271) (@lem5806336 B y x op)). Qed.
Lemma lem5806338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5806339 {B : Type'} (y : type402 B) (x : type402 B) (op : type1400 B) : (term632 B y x op) = (term633 B y x op).
Proof. exact (MK_COMB (@lem5806338) (@lem5806337 B y x op)). Qed.
Lemma lem5806340 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term634 B y z x op) = (term635 B y z x op).
Proof. exact (MK_COMB (@lem5806339 B y x op) (@lem5806270 B y z x op)). Qed.
Lemma lem5806345 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806346 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5806345 (type1400 B) Prop f x). Qed.
Lemma lem5806348 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5806346 B (@monoidal B) op). Qed.
Lemma lem5806349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5806350 {B : Type'} (op : type1400 B) : (term233 B op) = (term636 B op).
Proof. exact (MK_COMB (@lem5806349) (@lem5806348 B op)). Qed.
Lemma lem5806351 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) : (term483 B y z x op) = (term637 B y z x op).
Proof. exact (MK_COMB (@lem5806350 B op) (@lem5806340 B y z x op)). Qed.
Lemma lem5806352 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term485 B y z x) = (term638 B y z x).
Proof. exact (fun_ext (fun op : type1400 B => @lem5806351 B y z x op)). Qed.
Lemma lem5806353 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5806354 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term487 B y z x) = (term639 B y z x).
Proof. exact (MK_COMB (@lem5806353 B) (@lem5806352 B y z x)). Qed.
Lemma lem5806355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806356 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term540 B y z x) = (term640 B y z x).
Proof. exact (MK_COMB (@lem5806355) (@lem5806354 B y z x)). Qed.
Lemma lem5806357 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) : (term542 B y z x) = (term641 B y z x).
Proof. exact (MK_COMB (@lem5806356 B y z x) (@lem5806110 B)). Qed.
Lemma lem5806358 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term641 B y z x.
Proof. exact (EQ_MP (@lem5806357 B y z x) (@lem5805933 B y z x h1)). Qed.
Lemma lem5806359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5806360 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5806361 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5806366 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5806366 A B f x). Qed.
Lemma lem5806369 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem5806367 A B f x'). Qed.
Lemma lem5806374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806375 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5806374 (type1400 B) B f x). Qed.
Lemma lem5806377 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5806375 B (@neutral B) op). Qed.
Lemma lem5806378 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term57 A B op f x') = (term642 A B op f x').
Proof. exact (MK_COMB (@lem5806361 B op) (@lem5806369 A B f x')). Qed.
Lemma lem5806379 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term58 A B f x' op) = (term643 A B f x' op).
Proof. exact (MK_COMB (@lem5806378 A B op f x') (@lem5806377 B op)). Qed.
Lemma lem5806381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806382 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5806381 B (B -> B) f x). Qed.
Lemma lem5806383 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term642 A B op f x') = (term644 A B op f x').
Proof. exact (@lem5806382 B op (@I (A -> B) f x')). Qed.
Lemma lem5806384 {B : Type'} (op : type1400 B) : (@I ((B -> B -> B) -> B) (@neutral B) op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (eq_refl (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem5806385 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term643 A B f x' op) = (term645 A B f x' op).
Proof. exact (MK_COMB (@lem5806383 A B op f x') (@lem5806384 B op)). Qed.
Lemma lem5806387 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806388 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5806387 B B f x). Qed.
Lemma lem5806389 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term645 A B f x' op) = (term646 A B f x' op).
Proof. exact (@lem5806388 B (term644 A B op f x') (@I ((B -> B -> B) -> B) (@neutral B) op)). Qed.
Lemma lem5806390 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term643 A B f x' op) = (term646 A B f x' op).
Proof. exact (TRANS (@lem5806385 A B f x' op) (@lem5806389 A B f x' op)). Qed.
Lemma lem5806391 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term58 A B f x' op) = (term646 A B f x' op).
Proof. exact (TRANS (@lem5806379 A B f x' op) (@lem5806390 A B f x' op)). Qed.
Lemma lem5806396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806397 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5806396 A B f x). Qed.
Lemma lem5806399 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem5806397 A B f x'). Qed.
Lemma lem5806400 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term63 A B f x' op) = (term647 A B f x' op).
Proof. exact (MK_COMB (@lem5806360 B) (@lem5806391 A B f x' op)). Qed.
Lemma lem5806401 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : ((term58 A B f x' op) = (f x')) = ((term646 A B f x' op) = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem5806400 A B f x' op) (@lem5806399 A B f x')). Qed.
Lemma lem5806402 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term119 A B op f x') = (term648 A B op f x').
Proof. exact (MK_COMB (@lem5806359) (@lem5806401 A B op f x')). Qed.
Lemma lem5806407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5806408 {B : Type'} (f : type403 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> Prop) f x).
Proof. exact (@lem5806407 (type1400 B) Prop f x). Qed.
Lemma lem5806410 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5806408 B (@monoidal B) op). Qed.
Lemma lem5806411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806412 {B : Type'} (op : type1400 B) : (term132 B op) = (term649 B op).
Proof. exact (MK_COMB (@lem5806411) (@lem5806410 B op)). Qed.
Lemma lem5806413 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term168 A B op f x') = (term650 A B op f x').
Proof. exact (MK_COMB (@lem5806412 B op) (@lem5806402 A B op f x')). Qed.
Lemma lem5806414 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term650 A B op f x'.
Proof. exact (EQ_MP (@lem5806413 A B op f x') (@lem5805936 A B op f x' h1)). Qed.
Lemma lem5806417 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term593 B.
Proof. exact (proj2 (@lem5806358 B y z x h1)). Qed.
Lemma lem5806453 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5806454 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term243 B P Q) = (term242 B P Q).
Proof. exact (@lem5806453 B P Q). Qed.
Lemma lem5806455 {B : Type'} (op : type1400 B) : (term651 B op) = (term652 B op).
Proof. exact (@lem5806454 B (term576 B op) (term558 B op)). Qed.
Lemma lem5806456 {B : Type'} (op : type1400 B) (x : B) : (term653 B op x) = (term575 B op x).
Proof. exact (eq_refl (term653 B op x)). Qed.
Lemma lem5806457 {B : Type'} (op : type1400 B) : (term654 B op) = (term576 B op).
Proof. exact (fun_ext (fun x : B => @lem5806456 B op x)). Qed.
Lemma lem5806458 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806459 {B : Type'} (op : type1400 B) : (term655 B op) = (term577 B op).
Proof. exact (MK_COMB (@lem5806458 B) (@lem5806457 B op)). Qed.
Lemma lem5806460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806461 {B : Type'} (op : type1400 B) : (term656 B op) = (term578 B op).
Proof. exact (MK_COMB (@lem5806460) (@lem5806459 B op)). Qed.
Lemma lem5806462 {B : Type'} (op : type1400 B) (x : B) : (term657 B op x) = ((term555 B op x) = x).
Proof. exact (eq_refl (term657 B op x)). Qed.
Lemma lem5806463 {B : Type'} (op : type1400 B) : (term658 B op) = (term558 B op).
Proof. exact (fun_ext (fun x : B => @lem5806462 B op x)). Qed.
Lemma lem5806464 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806465 {B : Type'} (op : type1400 B) : (term659 B op) = (term559 B op).
Proof. exact (MK_COMB (@lem5806464 B) (@lem5806463 B op)). Qed.
Lemma lem5806466 {B : Type'} (op : type1400 B) : (term651 B op) = (term579 B op).
Proof. exact (MK_COMB (@lem5806461 B op) (@lem5806465 B op)). Qed.
Lemma lem5806467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806468 {B : Type'} (op : type1400 B) : (term660 B op) = (term661 B op).
Proof. exact (MK_COMB (@lem5806467) (@lem5806466 B op)). Qed.
Lemma lem5806469 {B : Type'} (op : type1400 B) (x : B) : (term653 B op x) = (term575 B op x).
Proof. exact (eq_refl (term653 B op x)). Qed.
Lemma lem5806470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806471 {B : Type'} (op : type1400 B) (x : B) : (term662 B op x) = (term663 B op x).
Proof. exact (MK_COMB (@lem5806470) (@lem5806469 B op x)). Qed.
Lemma lem5806472 {B : Type'} (op : type1400 B) (x : B) : (term657 B op x) = ((term555 B op x) = x).
Proof. exact (eq_refl (term657 B op x)). Qed.
Lemma lem5806473 {B : Type'} (op : type1400 B) (x : B) : (term664 B op x) = (term665 B op x).
Proof. exact (MK_COMB (@lem5806471 B op x) (@lem5806472 B op x)). Qed.
Lemma lem5806474 {B : Type'} (op : type1400 B) : (term666 B op) = (term667 B op).
Proof. exact (fun_ext (fun x : B => @lem5806473 B op x)). Qed.
Lemma lem5806475 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806476 {B : Type'} (op : type1400 B) : (term652 B op) = (term668 B op).
Proof. exact (MK_COMB (@lem5806475 B) (@lem5806474 B op)). Qed.
Lemma lem5806477 {B : Type'} (op : type1400 B) : ((term651 B op) = (term652 B op)) = ((term579 B op) = (term668 B op)).
Proof. exact (MK_COMB (@lem5806468 B op) (@lem5806476 B op)). Qed.
Lemma lem5806478 {B : Type'} (op : type1400 B) : (term579 B op) = (term668 B op).
Proof. exact (EQ_MP (@lem5806477 B op) (@lem5806455 B op)). Qed.
Lemma lem5806480 {A : Type'} (P : A -> Prop) (Q : Prop) : (term669 A P Q) = (term670 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5806481 {B : Type'} (P : B -> Prop) (Q : Prop) : (term669 B P Q) = (term670 B P Q).
Proof. exact (@lem5806480 B P Q). Qed.
Lemma lem5806482 {B : Type'} (op : type1400 B) (x : B) : (term671 B op x) = (term672 B op x).
Proof. exact (@lem5806481 B (term574 B op x) ((term555 B op x) = x)). Qed.
Lemma lem5806483 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term673 B op x y) = (term573 B op x y).
Proof. exact (eq_refl (term673 B op x y)). Qed.
Lemma lem5806484 {B : Type'} (op : type1400 B) (x : B) : (term674 B op x) = (term574 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806483 B op x y)). Qed.
Lemma lem5806485 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806486 {B : Type'} (op : type1400 B) (x : B) : (term675 B op x) = (term575 B op x).
Proof. exact (MK_COMB (@lem5806485 B) (@lem5806484 B op x)). Qed.
Lemma lem5806487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806488 {B : Type'} (op : type1400 B) (x : B) : (term676 B op x) = (term663 B op x).
Proof. exact (MK_COMB (@lem5806487) (@lem5806486 B op x)). Qed.
Lemma lem5806489 {B : Type'} (op : type1400 B) (x : B) : ((term555 B op x) = x) = ((term555 B op x) = x).
Proof. exact (eq_refl ((term555 B op x) = x)). Qed.
Lemma lem5806490 {B : Type'} (op : type1400 B) (x : B) : (term671 B op x) = (term665 B op x).
Proof. exact (MK_COMB (@lem5806488 B op x) (@lem5806489 B op x)). Qed.
Lemma lem5806491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806492 {B : Type'} (op : type1400 B) (x : B) : (term677 B op x) = (term678 B op x).
Proof. exact (MK_COMB (@lem5806491) (@lem5806490 B op x)). Qed.
Lemma lem5806493 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term673 B op x y) = (term573 B op x y).
Proof. exact (eq_refl (term673 B op x y)). Qed.
Lemma lem5806494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806495 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term679 B op x y) = (term680 B op x y).
Proof. exact (MK_COMB (@lem5806494) (@lem5806493 B op x y)). Qed.
Lemma lem5806496 {B : Type'} (op : type1400 B) (x : B) : ((term555 B op x) = x) = ((term555 B op x) = x).
Proof. exact (eq_refl ((term555 B op x) = x)). Qed.
Lemma lem5806497 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term681 B y op x) = (term682 B y op x).
Proof. exact (MK_COMB (@lem5806495 B op x y) (@lem5806496 B op x)). Qed.
Lemma lem5806498 {B : Type'} (op : type1400 B) (x : B) : (term683 B op x) = (term684 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806497 B y op x)). Qed.
Lemma lem5806499 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806500 {B : Type'} (op : type1400 B) (x : B) : (term672 B op x) = (term685 B op x).
Proof. exact (MK_COMB (@lem5806499 B) (@lem5806498 B op x)). Qed.
Lemma lem5806501 {B : Type'} (op : type1400 B) (x : B) : ((term671 B op x) = (term672 B op x)) = ((term665 B op x) = (term685 B op x)).
Proof. exact (MK_COMB (@lem5806492 B op x) (@lem5806500 B op x)). Qed.
Lemma lem5806502 {B : Type'} (op : type1400 B) (x : B) : (term665 B op x) = (term685 B op x).
Proof. exact (EQ_MP (@lem5806501 B op x) (@lem5806482 B op x)). Qed.
Lemma lem5806504 {A : Type'} (P : A -> Prop) (Q : Prop) : (term669 A P Q) = (term670 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5806505 {B : Type'} (P : B -> Prop) (Q : Prop) : (term669 B P Q) = (term670 B P Q).
Proof. exact (@lem5806504 B P Q). Qed.
Lemma lem5806506 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term686 B y op x) = (term687 B y op x).
Proof. exact (@lem5806505 B (term572 B op x y) ((term555 B op x) = x)). Qed.
Lemma lem5806507 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term688 B op x y z) = ((term563 B x op y z) = (term569 B op x y z)).
Proof. exact (eq_refl (term688 B op x y z)). Qed.
Lemma lem5806508 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term689 B op x y) = (term572 B op x y).
Proof. exact (fun_ext (fun z : B => @lem5806507 B op x y z)). Qed.
Lemma lem5806509 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806510 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term690 B op x y) = (term573 B op x y).
Proof. exact (MK_COMB (@lem5806509 B) (@lem5806508 B op x y)). Qed.
Lemma lem5806511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806512 {B : Type'} (op : type1400 B) (x : B) (y : B) : (term691 B op x y) = (term680 B op x y).
Proof. exact (MK_COMB (@lem5806511) (@lem5806510 B op x y)). Qed.
Lemma lem5806513 {B : Type'} (op : type1400 B) (x : B) : ((term555 B op x) = x) = ((term555 B op x) = x).
Proof. exact (eq_refl ((term555 B op x) = x)). Qed.
Lemma lem5806514 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term686 B y op x) = (term682 B y op x).
Proof. exact (MK_COMB (@lem5806512 B op x y) (@lem5806513 B op x)). Qed.
Lemma lem5806515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806516 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term692 B y op x) = (term693 B y op x).
Proof. exact (MK_COMB (@lem5806515) (@lem5806514 B y op x)). Qed.
Lemma lem5806517 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term688 B op x y z) = ((term563 B x op y z) = (term569 B op x y z)).
Proof. exact (eq_refl (term688 B op x y z)). Qed.
Lemma lem5806518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806519 {B : Type'} (op : type1400 B) (x : B) (y : B) (z : B) : (term694 B op x y z) = (term695 B op x y z).
Proof. exact (MK_COMB (@lem5806518) (@lem5806517 B op x y z)). Qed.
Lemma lem5806520 {B : Type'} (op : type1400 B) (x : B) : ((term555 B op x) = x) = ((term555 B op x) = x).
Proof. exact (eq_refl ((term555 B op x) = x)). Qed.
Lemma lem5806521 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term696 B y z op x) = (term697 B y z op x).
Proof. exact (MK_COMB (@lem5806519 B op x y z) (@lem5806520 B op x)). Qed.
Lemma lem5806522 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term698 B y op x) = (term699 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806521 B y z op x)). Qed.
Lemma lem5806523 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806524 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term687 B y op x) = (term700 B y op x).
Proof. exact (MK_COMB (@lem5806523 B) (@lem5806522 B y op x)). Qed.
Lemma lem5806525 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term686 B y op x) = (term687 B y op x)) = ((term682 B y op x) = (term700 B y op x)).
Proof. exact (MK_COMB (@lem5806516 B y op x) (@lem5806524 B y op x)). Qed.
Lemma lem5806526 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term682 B y op x) = (term700 B y op x).
Proof. exact (EQ_MP (@lem5806525 B y op x) (@lem5806506 B y op x)). Qed.
Lemma lem5806527 {B : Type'} (op : type1400 B) (x : B) : (term684 B op x) = (term701 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806526 B y op x)). Qed.
Lemma lem5806528 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806529 {B : Type'} (op : type1400 B) (x : B) : (term685 B op x) = (term702 B op x).
Proof. exact (MK_COMB (@lem5806528 B) (@lem5806527 B op x)). Qed.
Lemma lem5806530 {B : Type'} (op : type1400 B) (x : B) : (term665 B op x) = (term702 B op x).
Proof. exact (TRANS (@lem5806502 B op x) (@lem5806529 B op x)). Qed.
Lemma lem5806531 {B : Type'} (op : type1400 B) : (term667 B op) = (term703 B op).
Proof. exact (fun_ext (fun x : B => @lem5806530 B op x)). Qed.
Lemma lem5806532 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806533 {B : Type'} (op : type1400 B) : (term668 B op) = (term704 B op).
Proof. exact (MK_COMB (@lem5806532 B) (@lem5806531 B op)). Qed.
Lemma lem5806534 {B : Type'} (op : type1400 B) : (term579 B op) = (term704 B op).
Proof. exact (TRANS (@lem5806478 B op) (@lem5806533 B op)). Qed.
Lemma lem5806535 {B : Type'} (op : type1400 B) : (term586 B op) = (term586 B op).
Proof. exact (eq_refl (term586 B op)). Qed.
Lemma lem5806536 {B : Type'} (op : type1400 B) : (term587 B op) = (term705 B op).
Proof. exact (MK_COMB (@lem5806535 B op) (@lem5806534 B op)). Qed.
Lemma lem5806538 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5806539 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term243 B P Q) = (term242 B P Q).
Proof. exact (@lem5806538 B P Q). Qed.
Lemma lem5806540 {B : Type'} (op : type1400 B) : (term706 B op) = (term707 B op).
Proof. exact (@lem5806539 B (term584 B op) (term703 B op)). Qed.
Lemma lem5806541 {B : Type'} (op : type1400 B) (x : B) : (term708 B op x) = (term583 B op x).
Proof. exact (eq_refl (term708 B op x)). Qed.
Lemma lem5806542 {B : Type'} (op : type1400 B) : (term709 B op) = (term584 B op).
Proof. exact (fun_ext (fun x : B => @lem5806541 B op x)). Qed.
Lemma lem5806543 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806544 {B : Type'} (op : type1400 B) : (term710 B op) = (term585 B op).
Proof. exact (MK_COMB (@lem5806543 B) (@lem5806542 B op)). Qed.
Lemma lem5806545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806546 {B : Type'} (op : type1400 B) : (term711 B op) = (term586 B op).
Proof. exact (MK_COMB (@lem5806545) (@lem5806544 B op)). Qed.
Lemma lem5806547 {B : Type'} (op : type1400 B) (x : B) : (term712 B op x) = (term702 B op x).
Proof. exact (eq_refl (term712 B op x)). Qed.
Lemma lem5806548 {B : Type'} (op : type1400 B) : (term713 B op) = (term703 B op).
Proof. exact (fun_ext (fun x : B => @lem5806547 B op x)). Qed.
Lemma lem5806549 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806550 {B : Type'} (op : type1400 B) : (term714 B op) = (term704 B op).
Proof. exact (MK_COMB (@lem5806549 B) (@lem5806548 B op)). Qed.
Lemma lem5806551 {B : Type'} (op : type1400 B) : (term706 B op) = (term705 B op).
Proof. exact (MK_COMB (@lem5806546 B op) (@lem5806550 B op)). Qed.
Lemma lem5806552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806553 {B : Type'} (op : type1400 B) : (term715 B op) = (term716 B op).
Proof. exact (MK_COMB (@lem5806552) (@lem5806551 B op)). Qed.
Lemma lem5806554 {B : Type'} (op : type1400 B) (x : B) : (term708 B op x) = (term583 B op x).
Proof. exact (eq_refl (term708 B op x)). Qed.
Lemma lem5806555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806556 {B : Type'} (op : type1400 B) (x : B) : (term717 B op x) = (term718 B op x).
Proof. exact (MK_COMB (@lem5806555) (@lem5806554 B op x)). Qed.
Lemma lem5806557 {B : Type'} (op : type1400 B) (x : B) : (term712 B op x) = (term702 B op x).
Proof. exact (eq_refl (term712 B op x)). Qed.
Lemma lem5806558 {B : Type'} (op : type1400 B) (x : B) : (term719 B op x) = (term720 B op x).
Proof. exact (MK_COMB (@lem5806556 B op x) (@lem5806557 B op x)). Qed.
Lemma lem5806559 {B : Type'} (op : type1400 B) : (term721 B op) = (term722 B op).
Proof. exact (fun_ext (fun x : B => @lem5806558 B op x)). Qed.
Lemma lem5806560 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806561 {B : Type'} (op : type1400 B) : (term707 B op) = (term723 B op).
Proof. exact (MK_COMB (@lem5806560 B) (@lem5806559 B op)). Qed.
Lemma lem5806562 {B : Type'} (op : type1400 B) : ((term706 B op) = (term707 B op)) = ((term705 B op) = (term723 B op)).
Proof. exact (MK_COMB (@lem5806553 B op) (@lem5806561 B op)). Qed.
Lemma lem5806563 {B : Type'} (op : type1400 B) : (term705 B op) = (term723 B op).
Proof. exact (EQ_MP (@lem5806562 B op) (@lem5806540 B op)). Qed.
Lemma lem5806565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5806566 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term243 B P Q) = (term242 B P Q).
Proof. exact (@lem5806565 B P Q). Qed.
Lemma lem5806567 {B : Type'} (op : type1400 B) (x : B) : (term724 B op x) = (term725 B op x).
Proof. exact (@lem5806566 B (term582 B op x) (term701 B op x)). Qed.
Lemma lem5806568 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term726 B op x y) = ((term560 B op x y) = (term560 B op y x)).
Proof. exact (eq_refl (term726 B op x y)). Qed.
Lemma lem5806569 {B : Type'} (op : type1400 B) (x : B) : (term727 B op x) = (term582 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806568 B op y x)). Qed.
Lemma lem5806570 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806571 {B : Type'} (op : type1400 B) (x : B) : (term728 B op x) = (term583 B op x).
Proof. exact (MK_COMB (@lem5806570 B) (@lem5806569 B op x)). Qed.
Lemma lem5806572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806573 {B : Type'} (op : type1400 B) (x : B) : (term729 B op x) = (term718 B op x).
Proof. exact (MK_COMB (@lem5806572) (@lem5806571 B op x)). Qed.
Lemma lem5806574 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term730 B op x y) = (term700 B y op x).
Proof. exact (eq_refl (term730 B op x y)). Qed.
Lemma lem5806575 {B : Type'} (op : type1400 B) (x : B) : (term731 B op x) = (term701 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806574 B y op x)). Qed.
Lemma lem5806576 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806577 {B : Type'} (op : type1400 B) (x : B) : (term732 B op x) = (term702 B op x).
Proof. exact (MK_COMB (@lem5806576 B) (@lem5806575 B op x)). Qed.
Lemma lem5806578 {B : Type'} (op : type1400 B) (x : B) : (term724 B op x) = (term720 B op x).
Proof. exact (MK_COMB (@lem5806573 B op x) (@lem5806577 B op x)). Qed.
Lemma lem5806579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806580 {B : Type'} (op : type1400 B) (x : B) : (term733 B op x) = (term734 B op x).
Proof. exact (MK_COMB (@lem5806579) (@lem5806578 B op x)). Qed.
Lemma lem5806581 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term726 B op x y) = ((term560 B op x y) = (term560 B op y x)).
Proof. exact (eq_refl (term726 B op x y)). Qed.
Lemma lem5806582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5806583 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term735 B op x y) = (term736 B op y x).
Proof. exact (MK_COMB (@lem5806582) (@lem5806581 B op y x)). Qed.
Lemma lem5806584 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term730 B op x y) = (term700 B y op x).
Proof. exact (eq_refl (term730 B op x y)). Qed.
Lemma lem5806585 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term737 B op x y) = (term738 B y op x).
Proof. exact (MK_COMB (@lem5806583 B op y x) (@lem5806584 B y op x)). Qed.
Lemma lem5806586 {B : Type'} (op : type1400 B) (x : B) : (term739 B op x) = (term740 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806585 B y op x)). Qed.
Lemma lem5806587 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806588 {B : Type'} (op : type1400 B) (x : B) : (term725 B op x) = (term741 B op x).
Proof. exact (MK_COMB (@lem5806587 B) (@lem5806586 B op x)). Qed.
Lemma lem5806589 {B : Type'} (op : type1400 B) (x : B) : ((term724 B op x) = (term725 B op x)) = ((term720 B op x) = (term741 B op x)).
Proof. exact (MK_COMB (@lem5806580 B op x) (@lem5806588 B op x)). Qed.
Lemma lem5806590 {B : Type'} (op : type1400 B) (x : B) : (term720 B op x) = (term741 B op x).
Proof. exact (EQ_MP (@lem5806589 B op x) (@lem5806567 B op x)). Qed.
Lemma lem5806592 {A : Type'} (P : Prop) (Q : A -> Prop) : (term742 A P Q) = (term743 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5806593 {B : Type'} (P : Prop) (Q : B -> Prop) : (term742 B P Q) = (term743 B P Q).
Proof. exact (@lem5806592 B P Q). Qed.
Lemma lem5806594 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term744 B y op x) = (term745 B y op x).
Proof. exact (@lem5806593 B ((term560 B op x y) = (term560 B op y x)) (term699 B y op x)). Qed.
Lemma lem5806595 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term746 B y op x z) = (term697 B y z op x).
Proof. exact (eq_refl (term746 B y op x z)). Qed.
Lemma lem5806596 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term747 B y op x) = (term699 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806595 B y z op x)). Qed.
Lemma lem5806597 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806598 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term748 B y op x) = (term700 B y op x).
Proof. exact (MK_COMB (@lem5806597 B) (@lem5806596 B y op x)). Qed.
Lemma lem5806599 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term736 B op y x) = (term736 B op y x).
Proof. exact (eq_refl (term736 B op y x)). Qed.
Lemma lem5806600 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term744 B y op x) = (term738 B y op x).
Proof. exact (MK_COMB (@lem5806599 B op y x) (@lem5806598 B y op x)). Qed.
Lemma lem5806601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806602 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term749 B y op x) = (term750 B y op x).
Proof. exact (MK_COMB (@lem5806601) (@lem5806600 B y op x)). Qed.
Lemma lem5806603 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term746 B y op x z) = (term697 B y z op x).
Proof. exact (eq_refl (term746 B y op x z)). Qed.
Lemma lem5806604 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term736 B op y x) = (term736 B op y x).
Proof. exact (eq_refl (term736 B op y x)). Qed.
Lemma lem5806605 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term751 B y op x z) = (term752 B y z op x).
Proof. exact (MK_COMB (@lem5806604 B op y x) (@lem5806603 B y z op x)). Qed.
Lemma lem5806606 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term753 B y op x) = (term754 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806605 B y z op x)). Qed.
Lemma lem5806607 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806608 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term745 B y op x) = (term755 B y op x).
Proof. exact (MK_COMB (@lem5806607 B) (@lem5806606 B y op x)). Qed.
Lemma lem5806609 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term744 B y op x) = (term745 B y op x)) = ((term738 B y op x) = (term755 B y op x)).
Proof. exact (MK_COMB (@lem5806602 B y op x) (@lem5806608 B y op x)). Qed.
Lemma lem5806610 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term738 B y op x) = (term755 B y op x).
Proof. exact (EQ_MP (@lem5806609 B y op x) (@lem5806594 B y op x)). Qed.
Lemma lem5806611 {B : Type'} (op : type1400 B) (x : B) : (term740 B op x) = (term756 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806610 B y op x)). Qed.
Lemma lem5806612 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806613 {B : Type'} (op : type1400 B) (x : B) : (term741 B op x) = (term757 B op x).
Proof. exact (MK_COMB (@lem5806612 B) (@lem5806611 B op x)). Qed.
Lemma lem5806614 {B : Type'} (op : type1400 B) (x : B) : (term720 B op x) = (term757 B op x).
Proof. exact (TRANS (@lem5806590 B op x) (@lem5806613 B op x)). Qed.
Lemma lem5806615 {B : Type'} (op : type1400 B) : (term722 B op) = (term758 B op).
Proof. exact (fun_ext (fun x : B => @lem5806614 B op x)). Qed.
Lemma lem5806616 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806617 {B : Type'} (op : type1400 B) : (term723 B op) = (term759 B op).
Proof. exact (MK_COMB (@lem5806616 B) (@lem5806615 B op)). Qed.
Lemma lem5806618 {B : Type'} (op : type1400 B) : (term705 B op) = (term759 B op).
Proof. exact (TRANS (@lem5806563 B op) (@lem5806617 B op)). Qed.
Lemma lem5806619 {B : Type'} (op : type1400 B) : (term587 B op) = (term759 B op).
Proof. exact (TRANS (@lem5806536 B op) (@lem5806618 B op)). Qed.
Lemma lem5806620 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806621 {B : Type'} (op : type1400 B) : (term591 B op) = (term760 B op).
Proof. exact (MK_COMB (@lem5806620 B op) (@lem5806619 B op)). Qed.
Lemma lem5806623 {A : Type'} (P : Prop) (Q : A -> Prop) : (term761 A P Q) = (term762 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5806624 {B : Type'} (P : Prop) (Q : B -> Prop) : (term761 B P Q) = (term762 B P Q).
Proof. exact (@lem5806623 B P Q). Qed.
Lemma lem5806625 {B : Type'} (op : type1400 B) : (term763 B op) = (term764 B op).
Proof. exact (@lem5806624 B (term589 B op) (term758 B op)). Qed.
Lemma lem5806626 {B : Type'} (op : type1400 B) (x : B) : (term765 B op x) = (term757 B op x).
Proof. exact (eq_refl (term765 B op x)). Qed.
Lemma lem5806627 {B : Type'} (op : type1400 B) : (term766 B op) = (term758 B op).
Proof. exact (fun_ext (fun x : B => @lem5806626 B op x)). Qed.
Lemma lem5806628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806629 {B : Type'} (op : type1400 B) : (term767 B op) = (term759 B op).
Proof. exact (MK_COMB (@lem5806628 B) (@lem5806627 B op)). Qed.
Lemma lem5806630 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806631 {B : Type'} (op : type1400 B) : (term763 B op) = (term760 B op).
Proof. exact (MK_COMB (@lem5806630 B op) (@lem5806629 B op)). Qed.
Lemma lem5806632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806633 {B : Type'} (op : type1400 B) : (term768 B op) = (term769 B op).
Proof. exact (MK_COMB (@lem5806632) (@lem5806631 B op)). Qed.
Lemma lem5806634 {B : Type'} (op : type1400 B) (x : B) : (term765 B op x) = (term757 B op x).
Proof. exact (eq_refl (term765 B op x)). Qed.
Lemma lem5806635 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806636 {B : Type'} (op : type1400 B) (x : B) : (term770 B op x) = (term771 B op x).
Proof. exact (MK_COMB (@lem5806635 B op) (@lem5806634 B op x)). Qed.
Lemma lem5806637 {B : Type'} (op : type1400 B) : (term772 B op) = (term773 B op).
Proof. exact (fun_ext (fun x : B => @lem5806636 B op x)). Qed.
Lemma lem5806638 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806639 {B : Type'} (op : type1400 B) : (term764 B op) = (term774 B op).
Proof. exact (MK_COMB (@lem5806638 B) (@lem5806637 B op)). Qed.
Lemma lem5806640 {B : Type'} (op : type1400 B) : ((term763 B op) = (term764 B op)) = ((term760 B op) = (term774 B op)).
Proof. exact (MK_COMB (@lem5806633 B op) (@lem5806639 B op)). Qed.
Lemma lem5806641 {B : Type'} (op : type1400 B) : (term760 B op) = (term774 B op).
Proof. exact (EQ_MP (@lem5806640 B op) (@lem5806625 B op)). Qed.
Lemma lem5806643 {A : Type'} (P : Prop) (Q : A -> Prop) : (term761 A P Q) = (term762 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5806644 {B : Type'} (P : Prop) (Q : B -> Prop) : (term761 B P Q) = (term762 B P Q).
Proof. exact (@lem5806643 B P Q). Qed.
Lemma lem5806645 {B : Type'} (op : type1400 B) (x : B) : (term775 B op x) = (term776 B op x).
Proof. exact (@lem5806644 B (term589 B op) (term756 B op x)). Qed.
Lemma lem5806646 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term777 B op x y) = (term755 B y op x).
Proof. exact (eq_refl (term777 B op x y)). Qed.
Lemma lem5806647 {B : Type'} (op : type1400 B) (x : B) : (term778 B op x) = (term756 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806646 B y op x)). Qed.
Lemma lem5806648 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806649 {B : Type'} (op : type1400 B) (x : B) : (term779 B op x) = (term757 B op x).
Proof. exact (MK_COMB (@lem5806648 B) (@lem5806647 B op x)). Qed.
Lemma lem5806650 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806651 {B : Type'} (op : type1400 B) (x : B) : (term775 B op x) = (term771 B op x).
Proof. exact (MK_COMB (@lem5806650 B op) (@lem5806649 B op x)). Qed.
Lemma lem5806652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806653 {B : Type'} (op : type1400 B) (x : B) : (term780 B op x) = (term781 B op x).
Proof. exact (MK_COMB (@lem5806652) (@lem5806651 B op x)). Qed.
Lemma lem5806654 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term777 B op x y) = (term755 B y op x).
Proof. exact (eq_refl (term777 B op x y)). Qed.
Lemma lem5806655 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806656 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term782 B op x y) = (term783 B y op x).
Proof. exact (MK_COMB (@lem5806655 B op) (@lem5806654 B y op x)). Qed.
Lemma lem5806657 {B : Type'} (op : type1400 B) (x : B) : (term784 B op x) = (term785 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806656 B y op x)). Qed.
Lemma lem5806658 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806659 {B : Type'} (op : type1400 B) (x : B) : (term776 B op x) = (term786 B op x).
Proof. exact (MK_COMB (@lem5806658 B) (@lem5806657 B op x)). Qed.
Lemma lem5806660 {B : Type'} (op : type1400 B) (x : B) : ((term775 B op x) = (term776 B op x)) = ((term771 B op x) = (term786 B op x)).
Proof. exact (MK_COMB (@lem5806653 B op x) (@lem5806659 B op x)). Qed.
Lemma lem5806661 {B : Type'} (op : type1400 B) (x : B) : (term771 B op x) = (term786 B op x).
Proof. exact (EQ_MP (@lem5806660 B op x) (@lem5806645 B op x)). Qed.
Lemma lem5806663 {A : Type'} (P : Prop) (Q : A -> Prop) : (term761 A P Q) = (term762 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5806664 {B : Type'} (P : Prop) (Q : B -> Prop) : (term761 B P Q) = (term762 B P Q).
Proof. exact (@lem5806663 B P Q). Qed.
Lemma lem5806665 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term787 B y op x) = (term788 B y op x).
Proof. exact (@lem5806664 B (term589 B op) (term754 B y op x)). Qed.
Lemma lem5806666 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term789 B y op x z) = (term752 B y z op x).
Proof. exact (eq_refl (term789 B y op x z)). Qed.
Lemma lem5806667 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term790 B y op x) = (term754 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806666 B y z op x)). Qed.
Lemma lem5806668 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806669 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term791 B y op x) = (term755 B y op x).
Proof. exact (MK_COMB (@lem5806668 B) (@lem5806667 B y op x)). Qed.
Lemma lem5806670 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806671 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term787 B y op x) = (term783 B y op x).
Proof. exact (MK_COMB (@lem5806670 B op) (@lem5806669 B y op x)). Qed.
Lemma lem5806672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806673 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term792 B y op x) = (term793 B y op x).
Proof. exact (MK_COMB (@lem5806672) (@lem5806671 B y op x)). Qed.
Lemma lem5806674 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term789 B y op x z) = (term752 B y z op x).
Proof. exact (eq_refl (term789 B y op x z)). Qed.
Lemma lem5806675 {B : Type'} (op : type1400 B) : (term590 B op) = (term590 B op).
Proof. exact (eq_refl (term590 B op)). Qed.
Lemma lem5806676 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term794 B y op x z) = (term795 B y z op x).
Proof. exact (MK_COMB (@lem5806675 B op) (@lem5806674 B y z op x)). Qed.
Lemma lem5806677 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term796 B y op x) = (term797 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806676 B y z op x)). Qed.
Lemma lem5806678 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806679 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term788 B y op x) = (term798 B y op x).
Proof. exact (MK_COMB (@lem5806678 B) (@lem5806677 B y op x)). Qed.
Lemma lem5806680 {B : Type'} (y : B) (op : type1400 B) (x : B) : ((term787 B y op x) = (term788 B y op x)) = ((term783 B y op x) = (term798 B y op x)).
Proof. exact (MK_COMB (@lem5806673 B y op x) (@lem5806679 B y op x)). Qed.
Lemma lem5806681 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term783 B y op x) = (term798 B y op x).
Proof. exact (EQ_MP (@lem5806680 B y op x) (@lem5806665 B y op x)). Qed.
Lemma lem5806682 {B : Type'} (op : type1400 B) (x : B) : (term785 B op x) = (term799 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806681 B y op x)). Qed.
Lemma lem5806683 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806684 {B : Type'} (op : type1400 B) (x : B) : (term786 B op x) = (term800 B op x).
Proof. exact (MK_COMB (@lem5806683 B) (@lem5806682 B op x)). Qed.
Lemma lem5806685 {B : Type'} (op : type1400 B) (x : B) : (term771 B op x) = (term800 B op x).
Proof. exact (TRANS (@lem5806661 B op x) (@lem5806684 B op x)). Qed.
Lemma lem5806686 {B : Type'} (op : type1400 B) : (term773 B op) = (term801 B op).
Proof. exact (fun_ext (fun x : B => @lem5806685 B op x)). Qed.
Lemma lem5806687 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806688 {B : Type'} (op : type1400 B) : (term774 B op) = (term802 B op).
Proof. exact (MK_COMB (@lem5806687 B) (@lem5806686 B op)). Qed.
Lemma lem5806689 {B : Type'} (op : type1400 B) : (term760 B op) = (term802 B op).
Proof. exact (TRANS (@lem5806641 B op) (@lem5806688 B op)). Qed.
Lemma lem5806690 {B : Type'} (op : type1400 B) : (term591 B op) = (term802 B op).
Proof. exact (TRANS (@lem5806621 B op) (@lem5806689 B op)). Qed.
Lemma lem5806691 {B : Type'} : (term592 B) = (term803 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5806690 B op)). Qed.
Lemma lem5806692 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5806693 {B : Type'} : (term593 B) = (term804 B).
Proof. exact (MK_COMB (@lem5806692 B) (@lem5806691 B)). Qed.
Lemma lem5806707 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term795 B y z op x) = (term805 B y z op x).
Proof. exact (@lem19490 ((term560 B op x y) = (term560 B op y x)) (term589 B op) (term697 B y z op x)). Qed.
Lemma lem5806714 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term806 B y z op x) = (term807 B y z op x).
Proof. exact (@lem19490 ((term563 B x op y z) = (term569 B op x y z)) (term589 B op) ((term555 B op x) = x)). Qed.
Lemma lem5806717 {B : Type'} (op : type1400 B) (y : B) (x : B) : (term808 B op y x) = (term808 B op y x).
Proof. exact (eq_refl (term808 B op y x)). Qed.
Lemma lem5806718 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term805 B y z op x) = (term809 B y z op x).
Proof. exact (MK_COMB (@lem5806717 B op y x) (@lem5806714 B y z op x)). Qed.
Lemma lem5806720 {B : Type'} (y : B) (z : B) (op : type1400 B) (x : B) : (term795 B y z op x) = (term809 B y z op x).
Proof. exact (TRANS (@lem5806707 B y z op x) (@lem5806718 B y z op x)). Qed.
Lemma lem5806721 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term797 B y op x) = (term810 B y op x).
Proof. exact (fun_ext (fun z : B => @lem5806720 B y z op x)). Qed.
Lemma lem5806722 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806723 {B : Type'} (y : B) (op : type1400 B) (x : B) : (term798 B y op x) = (term811 B y op x).
Proof. exact (MK_COMB (@lem5806722 B) (@lem5806721 B y op x)). Qed.
Lemma lem5806724 {B : Type'} (op : type1400 B) (x : B) : (term799 B op x) = (term812 B op x).
Proof. exact (fun_ext (fun y : B => @lem5806723 B y op x)). Qed.
Lemma lem5806725 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806726 {B : Type'} (op : type1400 B) (x : B) : (term800 B op x) = (term813 B op x).
Proof. exact (MK_COMB (@lem5806725 B) (@lem5806724 B op x)). Qed.
Lemma lem5806727 {B : Type'} (op : type1400 B) : (term801 B op) = (term814 B op).
Proof. exact (fun_ext (fun x : B => @lem5806726 B op x)). Qed.
Lemma lem5806728 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5806729 {B : Type'} (op : type1400 B) : (term802 B op) = (term815 B op).
Proof. exact (MK_COMB (@lem5806728 B) (@lem5806727 B op)). Qed.
Lemma lem5806730 {B : Type'} : (term803 B) = (term816 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5806729 B op)). Qed.
Lemma lem5806731 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5806732 {B : Type'} : (term804 B) = (term817 B).
Proof. exact (MK_COMB (@lem5806731 B) (@lem5806730 B)). Qed.
Lemma lem5806733 {B : Type'} : (term593 B) = (term817 B).
Proof. exact (TRANS (@lem5806693 B) (@lem5806732 B)). Qed.
Lemma lem5806734 {B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term817 B.
Proof. exact (EQ_MP (@lem5806733 B) (@lem5806417 B y z x h1)). Qed.
Lemma lem5806738 {B : Type'} (_73494 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term818 B _73494.
Proof. exact (@lem5806734 B y z x h1 _73494). Qed.
Lemma lem5806739 {B : Type'} (_73494 : type1400 B) : (term818 B _73494) = (term815 B _73494).
Proof. exact (eq_refl (term818 B _73494)). Qed.
Lemma lem5806740 {B : Type'} (_73494 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term815 B _73494.
Proof. exact (EQ_MP (@lem5806739 B _73494) (@lem5806738 B _73494 y z x h1)). Qed.
Lemma lem5806741 {B : Type'} (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term819 B _73494 _73495.
Proof. exact (@lem5806740 B _73494 y z x h1 _73495). Qed.
Lemma lem5806742 {B : Type'} (_73494 : type1400 B) (_73495 : B) : (term819 B _73494 _73495) = (term813 B _73494 _73495).
Proof. exact (eq_refl (term819 B _73494 _73495)). Qed.
Lemma lem5806743 {B : Type'} (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term813 B _73494 _73495.
Proof. exact (EQ_MP (@lem5806742 B _73494 _73495) (@lem5806741 B _73494 _73495 y z x h1)). Qed.
Lemma lem5806744 {B : Type'} (_73494 : type1400 B) (_73495 : B) (_73496 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term820 B _73494 _73495 _73496.
Proof. exact (@lem5806743 B _73494 _73495 y z x h1 _73496). Qed.
Lemma lem5806745 {B : Type'} (_73496 : B) (_73494 : type1400 B) (_73495 : B) : (term820 B _73494 _73495 _73496) = (term811 B _73496 _73494 _73495).
Proof. exact (eq_refl (term820 B _73494 _73495 _73496)). Qed.
Lemma lem5806746 {B : Type'} (_73496 : B) (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term811 B _73496 _73494 _73495.
Proof. exact (EQ_MP (@lem5806745 B _73496 _73494 _73495) (@lem5806744 B _73494 _73495 _73496 y z x h1)). Qed.
Lemma lem5806747 {B : Type'} (_73496 : B) (_73494 : type1400 B) (_73495 : B) (_73497 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term821 B _73496 _73494 _73495 _73497.
Proof. exact (@lem5806746 B _73496 _73494 _73495 y z x h1 _73497). Qed.
Lemma lem5806748 {B : Type'} (_73496 : B) (_73497 : B) (_73494 : type1400 B) (_73495 : B) : (term821 B _73496 _73494 _73495 _73497) = (term809 B _73496 _73497 _73494 _73495).
Proof. exact (eq_refl (term821 B _73496 _73494 _73495 _73497)). Qed.
Lemma lem5806749 {B : Type'} (_73496 : B) (_73497 : B) (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term809 B _73496 _73497 _73494 _73495.
Proof. exact (EQ_MP (@lem5806748 B _73496 _73497 _73494 _73495) (@lem5806747 B _73496 _73494 _73495 _73497 y z x h1)). Qed.
Lemma lem5806750 {B : Type'} (_73496 : B) (_73497 : B) (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term807 B _73496 _73497 _73494 _73495.
Proof. exact (proj2 (@lem5806749 B _73496 _73497 _73494 _73495 y z x h1)). Qed.
Lemma lem5806757 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term648 A B op f x'.
Proof. exact (proj2 (@lem5806414 A B op f x' h1)). Qed.
Lemma lem5806777 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term822 B _73494 _73496 _73495.
Proof. exact (proj1 (@lem5806749 B _73496 (@el B) _73494 _73495 y z x h1)). Qed.
Lemma lem5806789 {B : Type'} (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term823 B _73494 _73495.
Proof. exact (proj2 (@lem5806750 B (@el B) (@el B) _73494 _73495 y z x h1)). Qed.
Lemma lem5806870 {B : Type'} (x : B) (y : B) (z : B) : term824 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5806884 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (proj1 (@lem5806414 A B op f x' h1)). Qed.
Lemma lem5806885 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term825 B op.
Proof. exact (fun h0 : term589 B op => @lem5806884 A B op f x' h1). Qed.
Lemma lem5806887 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5806888 {B : Type'} (op : type1400 B) : (term825 B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5806887 (@I ((B -> B -> B) -> Prop) (@monoidal B) op)). Qed.
Lemma lem5806889 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem5806888 B op) (@lem5806885 A B op f x' h1)). Qed.
Lemma lem5806895 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5806896 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : (term822 B _73494 _73496 _73495) = (term827 B _73496 _73495 _73494).
Proof. exact (@lem5806895 ((term560 B _73494 _73495 _73496) = (term560 B _73494 _73496 _73495)) (term589 B _73494)). Qed.
Lemma lem5806904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806905 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : (term828 B _73494 _73496 _73495) = (term829 B _73496 _73495 _73494).
Proof. exact (MK_COMB (@lem5806904) (@lem5806896 B _73496 _73495 _73494)). Qed.
Lemma lem5806913 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : (term827 B _73496 _73495 _73494) = (term827 B _73496 _73495 _73494).
Proof. exact (eq_refl (term827 B _73496 _73495 _73494)). Qed.
Lemma lem5806914 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : ((term822 B _73494 _73496 _73495) = (term827 B _73496 _73495 _73494)) = ((term827 B _73496 _73495 _73494) = (term827 B _73496 _73495 _73494)).
Proof. exact (MK_COMB (@lem5806905 B _73496 _73495 _73494) (@lem5806913 B _73496 _73495 _73494)). Qed.
Lemma lem5806916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5806917 (x : Prop) : (x = x) = True.
Proof. exact (@lem5806916 Prop x). Qed.
Lemma lem5806918 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : ((term827 B _73496 _73495 _73494) = (term827 B _73496 _73495 _73494)) = True.
Proof. exact (@lem5806917 (term827 B _73496 _73495 _73494)). Qed.
Lemma lem5806919 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : ((term822 B _73494 _73496 _73495) = (term827 B _73496 _73495 _73494)) = True.
Proof. exact (TRANS (@lem5806914 B _73496 _73495 _73494) (@lem5806918 B _73496 _73495 _73494)). Qed.
Lemma lem5806920 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : True = ((term822 B _73494 _73496 _73495) = (term827 B _73496 _73495 _73494)).
Proof. exact (SYM (@lem5806919 B _73496 _73495 _73494)). Qed.
Lemma lem5806921 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) : (term822 B _73494 _73496 _73495) = (term827 B _73496 _73495 _73494).
Proof. exact (EQ_MP (@lem5806920 B _73496 _73495 _73494) (@lem0)). Qed.
Lemma lem5806922 {B : Type'} (_73496 : B) (_73495 : B) (_73494 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term827 B _73496 _73495 _73494.
Proof. exact (EQ_MP (@lem5806921 B _73496 _73495 _73494) (@lem5806777 B _73494 _73496 _73495 y z x h1)). Qed.
Lemma lem5806924 (b : Prop) (a : Prop) : (a \/ b) = (term830 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5806925 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) : (term827 B _73496 _73495 _73494) = (term831 B _73494 _73496 _73495).
Proof. exact (@lem5806924 (term589 B _73494) ((term560 B _73494 _73495 _73496) = (term560 B _73494 _73496 _73495))). Qed.
Lemma lem5806927 (a : Prop) : (term832 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5806928 {B : Type'} (_73494 : type1400 B) : (term833 B _73494) = (@I ((B -> B -> B) -> Prop) (@monoidal B) _73494).
Proof. exact (@lem5806927 (@I ((B -> B -> B) -> Prop) (@monoidal B) _73494)). Qed.
Lemma lem5806929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5806930 {B : Type'} (_73494 : type1400 B) : (term834 B _73494) = (term835 B _73494).
Proof. exact (MK_COMB (@lem5806929) (@lem5806928 B _73494)). Qed.
Lemma lem5806931 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) : ((term560 B _73494 _73495 _73496) = (term560 B _73494 _73496 _73495)) = ((term560 B _73494 _73495 _73496) = (term560 B _73494 _73496 _73495)).
Proof. exact (eq_refl ((term560 B _73494 _73495 _73496) = (term560 B _73494 _73496 _73495))). Qed.
Lemma lem5806932 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) : (term831 B _73494 _73496 _73495) = (term836 B _73494 _73496 _73495).
Proof. exact (MK_COMB (@lem5806930 B _73494) (@lem5806931 B _73494 _73496 _73495)). Qed.
Lemma lem5806933 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) : (term827 B _73496 _73495 _73494) = (term836 B _73494 _73496 _73495).
Proof. exact (TRANS (@lem5806925 B _73494 _73496 _73495) (@lem5806932 B _73494 _73496 _73495)). Qed.
Lemma lem5806936 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term836 B _73494 _73496 _73495.
Proof. exact (EQ_MP (@lem5806933 B _73494 _73496 _73495) (@lem5806922 B _73496 _73495 _73494 y z x h1)). Qed.
Lemma lem5806937 {B : Type'} (_73494 : type1400 B) (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term836 B _73494 _73496 _73495.
Proof. exact (@lem5806936 B _73494 _73496 _73495 y z x h1). Qed.
Lemma lem5806938 {B : Type'} (op : type1400 B) (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term836 B op _73496 _73495.
Proof. exact (@lem5806937 B op _73496 _73495 y z x h1). Qed.
Lemma lem5806941 {A B : Type'} (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term560 B op _73495 _73496) = (term560 B op _73496 _73495).
Proof. exact (@lem5806938 B op _73496 _73495 y z x h1 (@lem5806889 A B op f x' h2)). Qed.
Lemma lem5806942 {A B : Type'} (_73496 : B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term560 B op _73495 _73496) = (term560 B op _73496 _73495).
Proof. exact (@lem5806941 A B _73496 _73495 y z x op f x' h1 h2). Qed.
Lemma lem5806943 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term837 A B op f x') = (term646 A B f x' op).
Proof. exact (@lem5806942 A B (@I (A -> B) f x') (@I ((B -> B -> B) -> B) (@neutral B) op) y z x op f x' h1 h2). Qed.
Lemma lem5806944 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : term838 A B f x' op.
Proof. exact (fun h0 : term839 A B f x' op => @lem5806943 A B y z x op f x' h1 h2). Qed.
Lemma lem5806946 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5806947 {A B : Type'} (f : A -> B) (x' : A) (op : type1400 B) : (term838 A B f x' op) = ((term837 A B op f x') = (term646 A B f x' op)).
Proof. exact (@lem5806946 ((term837 A B op f x') = (term646 A B f x' op))). Qed.
Lemma lem5806948 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term837 A B op f x') = (term646 A B f x' op).
Proof. exact (EQ_MP (@lem5806947 A B f x' op) (@lem5806944 A B y z x op f x' h1 h2)). Qed.
Lemma lem5806950 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (proj1 (@lem5806414 A B op f x' h1)). Qed.
Lemma lem5806951 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term825 B op.
Proof. exact (fun h0 : term589 B op => @lem5806950 A B op f x' h1). Qed.
Lemma lem5806953 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5806954 {B : Type'} (op : type1400 B) : (term825 B op) = (@I ((B -> B -> B) -> Prop) (@monoidal B) op).
Proof. exact (@lem5806953 (@I ((B -> B -> B) -> Prop) (@monoidal B) op)). Qed.
Lemma lem5806955 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : @I ((B -> B -> B) -> Prop) (@monoidal B) op.
Proof. exact (EQ_MP (@lem5806954 B op) (@lem5806951 A B op f x' h1)). Qed.
Lemma lem5806961 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5806962 {B : Type'} (_73495 : B) (_73494 : type1400 B) : (term823 B _73494 _73495) = (term840 B _73495 _73494).
Proof. exact (@lem5806961 ((term555 B _73494 _73495) = _73495) (term589 B _73494)). Qed.
Lemma lem5806970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5806971 {B : Type'} (_73495 : B) (_73494 : type1400 B) : (term841 B _73494 _73495) = (term842 B _73495 _73494).
Proof. exact (MK_COMB (@lem5806970) (@lem5806962 B _73495 _73494)). Qed.
Lemma lem5806979 {B : Type'} (_73495 : B) (_73494 : type1400 B) : (term840 B _73495 _73494) = (term840 B _73495 _73494).
Proof. exact (eq_refl (term840 B _73495 _73494)). Qed.
Lemma lem5806980 {B : Type'} (_73495 : B) (_73494 : type1400 B) : ((term823 B _73494 _73495) = (term840 B _73495 _73494)) = ((term840 B _73495 _73494) = (term840 B _73495 _73494)).
Proof. exact (MK_COMB (@lem5806971 B _73495 _73494) (@lem5806979 B _73495 _73494)). Qed.
Lemma lem5806982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5806983 (x : Prop) : (x = x) = True.
Proof. exact (@lem5806982 Prop x). Qed.
Lemma lem5806984 {B : Type'} (_73495 : B) (_73494 : type1400 B) : ((term840 B _73495 _73494) = (term840 B _73495 _73494)) = True.
Proof. exact (@lem5806983 (term840 B _73495 _73494)). Qed.
Lemma lem5806985 {B : Type'} (_73495 : B) (_73494 : type1400 B) : ((term823 B _73494 _73495) = (term840 B _73495 _73494)) = True.
Proof. exact (TRANS (@lem5806980 B _73495 _73494) (@lem5806984 B _73495 _73494)). Qed.
Lemma lem5806986 {B : Type'} (_73495 : B) (_73494 : type1400 B) : True = ((term823 B _73494 _73495) = (term840 B _73495 _73494)).
Proof. exact (SYM (@lem5806985 B _73495 _73494)). Qed.
Lemma lem5806987 {B : Type'} (_73495 : B) (_73494 : type1400 B) : (term823 B _73494 _73495) = (term840 B _73495 _73494).
Proof. exact (EQ_MP (@lem5806986 B _73495 _73494) (@lem0)). Qed.
Lemma lem5806988 {B : Type'} (_73495 : B) (_73494 : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term840 B _73495 _73494.
Proof. exact (EQ_MP (@lem5806987 B _73495 _73494) (@lem5806789 B _73494 _73495 y z x h1)). Qed.
Lemma lem5806990 (b : Prop) (a : Prop) : (a \/ b) = (term830 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5806991 {B : Type'} (_73494 : type1400 B) (_73495 : B) : (term840 B _73495 _73494) = (term843 B _73494 _73495).
Proof. exact (@lem5806990 (term589 B _73494) ((term555 B _73494 _73495) = _73495)). Qed.
Lemma lem5806993 (a : Prop) : (term832 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5806994 {B : Type'} (_73494 : type1400 B) : (term833 B _73494) = (@I ((B -> B -> B) -> Prop) (@monoidal B) _73494).
Proof. exact (@lem5806993 (@I ((B -> B -> B) -> Prop) (@monoidal B) _73494)). Qed.
Lemma lem5806995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5806996 {B : Type'} (_73494 : type1400 B) : (term834 B _73494) = (term835 B _73494).
Proof. exact (MK_COMB (@lem5806995) (@lem5806994 B _73494)). Qed.
Lemma lem5806997 {B : Type'} (_73494 : type1400 B) (_73495 : B) : ((term555 B _73494 _73495) = _73495) = ((term555 B _73494 _73495) = _73495).
Proof. exact (eq_refl ((term555 B _73494 _73495) = _73495)). Qed.
Lemma lem5806998 {B : Type'} (_73494 : type1400 B) (_73495 : B) : (term843 B _73494 _73495) = (term844 B _73494 _73495).
Proof. exact (MK_COMB (@lem5806996 B _73494) (@lem5806997 B _73494 _73495)). Qed.
Lemma lem5806999 {B : Type'} (_73494 : type1400 B) (_73495 : B) : (term840 B _73495 _73494) = (term844 B _73494 _73495).
Proof. exact (TRANS (@lem5806991 B _73494 _73495) (@lem5806998 B _73494 _73495)). Qed.
Lemma lem5807002 {B : Type'} (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term844 B _73494 _73495.
Proof. exact (EQ_MP (@lem5806999 B _73494 _73495) (@lem5806988 B _73495 _73494 y z x h1)). Qed.
Lemma lem5807003 {B : Type'} (_73494 : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term844 B _73494 _73495.
Proof. exact (@lem5807002 B _73494 _73495 y z x h1). Qed.
Lemma lem5807004 {B : Type'} (op : type1400 B) (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term542 B y z x) : term844 B op _73495.
Proof. exact (@lem5807003 B op _73495 y z x h1). Qed.
Lemma lem5807007 {A B : Type'} (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term555 B op _73495) = _73495.
Proof. exact (@lem5807004 B op _73495 y z x h1 (@lem5806955 A B op f x' h2)). Qed.
Lemma lem5807008 {A B : Type'} (_73495 : B) (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term555 B op _73495) = _73495.
Proof. exact (@lem5807007 A B _73495 y z x op f x' h1 h2). Qed.
Lemma lem5807009 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term837 A B op f x') = (@I (A -> B) f x').
Proof. exact (@lem5807008 A B (@I (A -> B) f x') y z x op f x' h1 h2). Qed.
Lemma lem5807010 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : term845 A B op f x'.
Proof. exact (fun h0 : term846 A B op f x' => @lem5807009 A B y z x op f x' h1 h2). Qed.
Lemma lem5807012 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5807013 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term845 A B op f x') = ((term837 A B op f x') = (@I (A -> B) f x')).
Proof. exact (@lem5807012 ((term837 A B op f x') = (@I (A -> B) f x'))). Qed.
Lemma lem5807014 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term837 A B op f x') = (@I (A -> B) f x').
Proof. exact (EQ_MP (@lem5807013 A B op f x') (@lem5807010 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807032 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5807033 {B : Type'} (y : B) (x : B) (z : B) : (term847 B x y z) = (term848 B y x z).
Proof. exact (@lem5807032 (y = z) (term849 B x z)). Qed.
Lemma lem5807043 {B : Type'} (x : B) (y : B) : (term850 B x y) = (term850 B x y).
Proof. exact (eq_refl (term850 B x y)). Qed.
Lemma lem5807044 {B : Type'} (y : B) (x : B) (z : B) : (term824 B x y z) = (term851 B y x z).
Proof. exact (MK_COMB (@lem5807043 B x y) (@lem5807033 B y x z)). Qed.
Lemma lem5807048 (q : Prop) (p : Prop) (r : Prop) : (term852 p q r) = (term852 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5807049 {B : Type'} (y : B) (x : B) (z : B) : (term851 B y x z) = (term853 B y x z).
Proof. exact (@lem5807048 (y = z) (term849 B x y) (term849 B x z)). Qed.
Lemma lem5807071 {B : Type'} (y : B) (x : B) (z : B) : (term824 B x y z) = (term853 B y x z).
Proof. exact (TRANS (@lem5807044 B y x z) (@lem5807049 B y x z)). Qed.
Lemma lem5807072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5807073 {B : Type'} (y : B) (x : B) (z : B) : (term854 B x y z) = (term855 B y x z).
Proof. exact (MK_COMB (@lem5807072) (@lem5807071 B y x z)). Qed.
Lemma lem5807095 {B : Type'} (y : B) (x : B) (z : B) : (term853 B y x z) = (term853 B y x z).
Proof. exact (eq_refl (term853 B y x z)). Qed.
Lemma lem5807096 {B : Type'} (y : B) (x : B) (z : B) : ((term824 B x y z) = (term853 B y x z)) = ((term853 B y x z) = (term853 B y x z)).
Proof. exact (MK_COMB (@lem5807073 B y x z) (@lem5807095 B y x z)). Qed.
Lemma lem5807098 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5807099 (x : Prop) : (x = x) = True.
Proof. exact (@lem5807098 Prop x). Qed.
Lemma lem5807100 {B : Type'} (y : B) (x : B) (z : B) : ((term853 B y x z) = (term853 B y x z)) = True.
Proof. exact (@lem5807099 (term853 B y x z)). Qed.
Lemma lem5807101 {B : Type'} (y : B) (x : B) (z : B) : ((term824 B x y z) = (term853 B y x z)) = True.
Proof. exact (TRANS (@lem5807096 B y x z) (@lem5807100 B y x z)). Qed.
Lemma lem5807102 {B : Type'} (y : B) (x : B) (z : B) : True = ((term824 B x y z) = (term853 B y x z)).
Proof. exact (SYM (@lem5807101 B y x z)). Qed.
Lemma lem5807103 {B : Type'} (y : B) (x : B) (z : B) : (term824 B x y z) = (term853 B y x z).
Proof. exact (EQ_MP (@lem5807102 B y x z) (@lem0)). Qed.
Lemma lem5807104 {B : Type'} (y : B) (x : B) (z : B) : term853 B y x z.
Proof. exact (EQ_MP (@lem5807103 B y x z) (@lem5806870 B x y z)). Qed.
Lemma lem5807106 (b : Prop) (a : Prop) : (a \/ b) = (term830 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5807107 {B : Type'} (x : B) (y : B) (z : B) : (term853 B y x z) = (term856 B x y z).
Proof. exact (@lem5807106 (term857 B y x z) (y = z)). Qed.
Lemma lem5807109 (a : Prop) (b : Prop) : (term858 a b) = (term859 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5807110 {B : Type'} (y : B) (x : B) (z : B) : (term860 B y x z) = (term861 B y x z).
Proof. exact (@lem5807109 (term849 B x y) (term849 B x z)). Qed.
Lemma lem5807112 (a : Prop) : (term832 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5807113 {B : Type'} (x : B) (y : B) : (term862 B x y) = (x = y).
Proof. exact (@lem5807112 (x = y)). Qed.
Lemma lem5807114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807115 {B : Type'} (x : B) (y : B) : (term863 B x y) = (term864 B x y).
Proof. exact (MK_COMB (@lem5807114) (@lem5807113 B x y)). Qed.
Lemma lem5807117 (a : Prop) : (term832 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5807118 {B : Type'} (x : B) (z : B) : (term862 B x z) = (x = z).
Proof. exact (@lem5807117 (x = z)). Qed.
Lemma lem5807119 {B : Type'} (y : B) (x : B) (z : B) : (term861 B y x z) = (term865 B y x z).
Proof. exact (MK_COMB (@lem5807115 B x y) (@lem5807118 B x z)). Qed.
Lemma lem5807120 {B : Type'} (y : B) (x : B) (z : B) : (term860 B y x z) = (term865 B y x z).
Proof. exact (TRANS (@lem5807110 B y x z) (@lem5807119 B y x z)). Qed.
Lemma lem5807121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807122 {B : Type'} (y : B) (x : B) (z : B) : (term866 B y x z) = (term867 B y x z).
Proof. exact (MK_COMB (@lem5807121) (@lem5807120 B y x z)). Qed.
Lemma lem5807123 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5807124 {B : Type'} (x : B) (y : B) (z : B) : (term856 B x y z) = (term868 B x y z).
Proof. exact (MK_COMB (@lem5807122 B y x z) (@lem5807123 B y z)). Qed.
Lemma lem5807125 {B : Type'} (x : B) (y : B) (z : B) : (term853 B y x z) = (term868 B x y z).
Proof. exact (TRANS (@lem5807107 B x y z) (@lem5807124 B x y z)). Qed.
Lemma lem5807127 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : term869 A B op f x'.
Proof. exact (conj (@lem5806948 A B y z x op f x' h1 h2) (@lem5807014 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807129 {B : Type'} (x : B) (y : B) (z : B) : term868 B x y z.
Proof. exact (EQ_MP (@lem5807125 B x y z) (@lem5807104 B y x z)). Qed.
Lemma lem5807130 {B : Type'} (x : B) (y : B) (z : B) : term868 B x y z.
Proof. exact (@lem5807129 B x y z). Qed.
Lemma lem5807131 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : term870 A B op f x'.
Proof. exact (@lem5807130 B (term837 A B op f x') (term646 A B f x' op) (@I (A -> B) f x')). Qed.
Lemma lem5807134 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term646 A B f x' op) = (@I (A -> B) f x').
Proof. exact (@lem5807131 A B op f x' (@lem5807127 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807135 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : term871 A B op f x'.
Proof. exact (fun h0 : term648 A B op f x' => @lem5807134 A B y z x op f x' h1 h2). Qed.
Lemma lem5807137 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5807138 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term871 A B op f x') = ((term646 A B f x' op) = (@I (A -> B) f x')).
Proof. exact (@lem5807137 ((term646 A B f x' op) = (@I (A -> B) f x'))). Qed.
Lemma lem5807139 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : (term646 A B f x' op) = (@I (A -> B) f x').
Proof. exact (EQ_MP (@lem5807138 A B op f x') (@lem5807135 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807142 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5807144 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) : (term648 A B op f x') = (term872 A B op f x').
Proof. exact (@lem5807142 ((term646 A B f x' op) = (@I (A -> B) f x'))). Qed.
Lemma lem5807147 {A B : Type'} (op : type1400 B) (f : A -> B) (x' : A) (h1 : term168 A B op f x') : term872 A B op f x'.
Proof. exact (EQ_MP (@lem5807144 A B op f x') (@lem5806757 A B op f x' h1)). Qed.
Lemma lem5807150 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : False.
Proof. exact (@lem5807147 A B op f x' h2 (@lem5807139 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807151 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : term873.
Proof. exact (fun h0 : ~ False => @lem5807150 A B y z x op f x' h1 h2). Qed.
Lemma lem5807153 (p : Prop) : (term826 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5807154 : term873 = False.
Proof. exact (@lem5807153 False). Qed.
Lemma lem5807155 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (op : type1400 B) (f : A -> B) (x' : A) (h1 : term542 B y z x) (h2 : term168 A B op f x') : False.
Proof. exact (EQ_MP (@lem5807154) (@lem5807151 A B y z x op f x' h1 h2)). Qed.
Lemma lem5807156 {A B : Type'} (op : type1400 B) (f : A -> B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term171 A B op f) (h2 : term542 B y z x) : False.
Proof. exact (ex_elim (@lem5805935 A B op f h1) (fun x' : A => fun h0 : term170 A B op f x' => @lem5807155 A B y z x op f x' h2 h0)). Qed.
Lemma lem5807157 {A B : Type'} (op : type1400 B) (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term173 A B op) (h2 : term542 B y z x) : False.
Proof. exact (ex_elim (@lem5805934 A B op h1) (fun f : A -> B => fun h0 : term172 A B op f => @lem5807156 A B op f y z x h0 h2)). Qed.
Lemma lem5807158 {A B : Type'} (y : type402 B) (z : type402 B) (x : type402 B) (h1 : term81 A B) (h2 : term542 B y z x) : False.
Proof. exact (ex_elim (@lem5805234 A B h1) (fun op : type1400 B => fun h0 : term174 A B op => @lem5807157 A B op y z x h0 h2)). Qed.
Lemma lem5807159 {A B : Type'} (y : type402 B) (x : type402 B) (h1 : term545 B y x) (h2 : term81 A B) : False.
Proof. exact (ex_elim (@lem5805932 B y x h1) (fun z : type402 B => fun h0 : term544 B y x z => @lem5807158 A B y z x h2 h0)). Qed.
Lemma lem5807160 {A B : Type'} (x : type402 B) (h1 : term547 B x) (h2 : term81 A B) : False.
Proof. exact (ex_elim (@lem5805931 B x h1) (fun y : type402 B => fun h0 : term546 B x y => @lem5807159 A B y x h0 h2)). Qed.
Lemma lem5807161 {A B : Type'} (h1 : term82 B) (h2 : term81 A B) : False.
Proof. exact (ex_elim (@lem5805930 B h1) (fun x : type402 B => fun h0 : term548 B x => @lem5807160 A B x h0 h2)). Qed.
Lemma lem5807162 {A B : Type'} (h1 : term81 A B) : term87 B.
Proof. exact (fun h0 : term82 B => @lem5807161 A B h0 h1). Qed.
Lemma lem5807163 {B : Type'} : (term87 B) = (term88 B).
Proof. exact (@lem69 (term82 B)). Qed.
Lemma lem5807164 {A B : Type'} (h1 : term81 A B) : term88 B.
Proof. exact (EQ_MP (@lem5807163 B) (@lem5807162 A B h1)). Qed.
Lemma lem5807165 {A B : Type'} : term90 A B.
Proof. exact (fun h0 : term81 A B => @lem5807164 A B h0). Qed.
Lemma lem5807166 {A B : Type'} : term83 A B.
Proof. exact (EQ_MP (@lem5805108 A B) (@lem5807165 A B)). Qed.
Lemma lem5807168 {A B : Type'} : term83 A B.
Proof. exact (@lem5804922 A B (@lem5807166 A B)). Qed.
Lemma lem5807169 {A B : Type'} (h1 : term81 A B) : term87 B.
Proof. exact (@lem5807168 A B (@lem5804903 A B h1)). Qed.
Lemma lem5807170 {A B : Type'} (h1 : term81 A B) : False.
Proof. exact (@lem5807169 A B h1 (@lem5804904 B)). Qed.
Lemma lem5807171 {A B : Type'} (h1 : term81 A B) : (term81 A B) = False.
Proof. exact (prop_ext (fun h2 : term81 A B => @lem5807170 A B h1) (fun h2 : False => @lem5804903 A B h1)). Qed.
Lemma lem5807172 {A B : Type'} (h1 : term81 A B) : False.
Proof. exact (EQ_MP (@lem5807171 A B h1) (@lem5804903 A B h1)). Qed.
Lemma lem5807173 {A B : Type'} : term80 A B.
Proof. exact (fun h0 : term81 A B => @lem5807172 A B h0). Qed.
Lemma lem5807174 {A B : Type'} : term78 A B.
Proof. exact (EQ_MP (@lem5804902 A B) (@lem5807173 A B)). Qed.
Lemma lem5807175 {A B : Type'} : term77 A B.
Proof. exact (EQ_MP (@lem5804898 A B) (@lem5807174 A B)). Qed.
