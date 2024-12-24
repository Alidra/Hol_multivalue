Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_RELATED_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5782567 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5782568 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem5782567 A h1 P). Qed.
Lemma lem5782569 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5782570 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem5782569 A P) (@lem5782568 A P h1)). Qed.
Lemma lem5782571 {A : Type'} (P : type686 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem5782572 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5782570 A P h1 (@lem5782571 A P h2)). Qed.
Lemma lem5782573 {A : Type'} (P : type686 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem5782572 A P h0 h1). Qed.
Lemma lem5782574 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5782575 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5782573 A P h2 (@lem5782574 A h1)). Qed.
Lemma lem5782576 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem5782575 A P h1 h0). Qed.
Lemma lem5782577 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem5782576 A P h1). Qed.
Lemma lem5782578 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem5782577 A h0). Qed.
Lemma lem5782579 {A : Type'} : term0 A.
Proof. exact (@lem5782578 A (@lem3558722 A)). Qed.
Lemma lem5782580 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem5782579 A P). Qed.
Lemma lem5782581 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5782583 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5782584 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term7 B R op) : term7 B R op.
Proof. exact (h1). Qed.
Lemma lem5782585 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term8 B R op.
Proof. exact (h1). Qed.
Lemma lem5782586 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term9 B R op) : term9 B R op.
Proof. exact (h1). Qed.
Lemma lem5782592 (p : Prop) (q : Prop) (r : Prop) : (term10 p q r) = (term11 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5782593 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term12 A B R f op s g) = (term13 A B R f op s g).
Proof. exact (@lem5782592 (@FINITE A s) (term14 A B s R f g) (term15 A B R f op s g)). Qed.
Lemma lem5782604 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term16 A B R f op g) = (term17 A B R f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5782593 A B R f op s g)). Qed.
Lemma lem5782605 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5782606 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term18 A B R f op g) = (term19 A B R f op g).
Proof. exact (MK_COMB (@lem5782605 A) (@lem5782604 A B R f op g)). Qed.
Lemma lem5782611 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term19 A B R f op g) = (term18 A B R f op g).
Proof. exact (SYM (@lem5782606 A B R f op g)). Qed.
Lemma lem5782613 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem5782581 A P) (@lem5782580 A P)). Qed.
Lemma lem5782614 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (@lem5782613 A P). Qed.
Lemma lem5782615 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : term20 A B R f op g.
Proof. exact (@lem5782614 A (term21 A B R f op g)). Qed.
Lemma lem5782616 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term22 A B R f op g) = (term23 A B R f op g).
Proof. exact (eq_refl (term22 A B R f op g)). Qed.
Lemma lem5782617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782618 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term24 A B R f op g) = (term25 A B R f op g).
Proof. exact (MK_COMB (@lem5782617) (@lem5782616 A B R f op g)). Qed.
Lemma lem5782619 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term26 A B R f op g s) = (term27 A B R f op s g).
Proof. exact (eq_refl (term26 A B R f op g s)). Qed.
Lemma lem5782620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782621 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term28 A B R f op g s) = (term29 A B R f op s g).
Proof. exact (MK_COMB (@lem5782620) (@lem5782619 A B R f op s g)). Qed.
Lemma lem5782622 {A : Type'} (x : A) (s : A -> Prop) : (term30 A x s) = (term30 A x s).
Proof. exact (eq_refl (term30 A x s)). Qed.
Lemma lem5782623 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term31 A B R f op g x s) = (term32 A B R f op g x s).
Proof. exact (MK_COMB (@lem5782621 A B R f op s g) (@lem5782622 A x s)). Qed.
Lemma lem5782624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5782625 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term33 A B R f op g x s) = (term34 A B R f op g x s).
Proof. exact (MK_COMB (@lem5782624) (@lem5782623 A B R f op g x s)). Qed.
Lemma lem5782626 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term35 A B R f op g x s) = (term36 A B R f op x s g).
Proof. exact (eq_refl (term35 A B R f op g x s)). Qed.
Lemma lem5782627 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term37 A B R f op g x s) = (term38 A B R f op x s g).
Proof. exact (MK_COMB (@lem5782625 A B R f op g x s) (@lem5782626 A B R f op x s g)). Qed.
Lemma lem5782628 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term39 A B R f op g x) = (term40 A B R f op x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5782627 A B R f op x s g)). Qed.
Lemma lem5782629 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5782630 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term41 A B R f op g x) = (term42 A B R f op x g).
Proof. exact (MK_COMB (@lem5782629 A) (@lem5782628 A B R f op x g)). Qed.
Lemma lem5782631 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term43 A B R f op g) = (term44 A B R f op g).
Proof. exact (fun_ext (fun x : A => @lem5782630 A B R f op x g)). Qed.
Lemma lem5782632 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5782633 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term45 A B R f op g) = (term46 A B R f op g).
Proof. exact (MK_COMB (@lem5782632 A) (@lem5782631 A B R f op g)). Qed.
Lemma lem5782634 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term47 A B R f op g) = (term48 A B R f op g).
Proof. exact (MK_COMB (@lem5782618 A B R f op g) (@lem5782633 A B R f op g)). Qed.
Lemma lem5782635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5782636 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term49 A B R f op g) = (term50 A B R f op g).
Proof. exact (MK_COMB (@lem5782635) (@lem5782634 A B R f op g)). Qed.
Lemma lem5782637 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term26 A B R f op g s) = (term27 A B R f op s g).
Proof. exact (eq_refl (term26 A B R f op g s)). Qed.
Lemma lem5782638 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (eq_refl (term51 A s)). Qed.
Lemma lem5782639 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term52 A B R f op g s) = (term13 A B R f op s g).
Proof. exact (MK_COMB (@lem5782638 A s) (@lem5782637 A B R f op s g)). Qed.
Lemma lem5782640 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term53 A B R f op g) = (term17 A B R f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5782639 A B R f op s g)). Qed.
Lemma lem5782641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5782642 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term54 A B R f op g) = (term19 A B R f op g).
Proof. exact (MK_COMB (@lem5782641 A) (@lem5782640 A B R f op g)). Qed.
Lemma lem5782643 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term20 A B R f op g) = (term55 A B R f op g).
Proof. exact (MK_COMB (@lem5782636 A B R f op g) (@lem5782642 A B R f op g)). Qed.
Lemma lem5782644 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : term55 A B R f op g.
Proof. exact (EQ_MP (@lem5782643 A B R f op g) (@lem5782615 A B R f op g)). Qed.
Lemma lem5782645 {A : Type'} (x : A) : term56 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5782646 {A : Type'} (x : A) : (term56 A x) = (term57 A x).
Proof. exact (eq_refl (term56 A x)). Qed.
Lemma lem5782647 {A : Type'} (x : A) : term57 A x.
Proof. exact (EQ_MP (@lem5782646 A x) (@lem5782645 A x)). Qed.
Lemma lem5782648 {A : Type'} (x : A) (y : A) : term58 A x y.
Proof. exact (@lem5782647 A x y). Qed.
Lemma lem5782649 {A : Type'} (y : A) (x : A) : (term58 A x y) = (term59 A y x).
Proof. exact (eq_refl (term58 A x y)). Qed.
Lemma lem5782650 {A : Type'} (y : A) (x : A) : term59 A y x.
Proof. exact (EQ_MP (@lem5782649 A y x) (@lem5782648 A x y)). Qed.
Lemma lem5782651 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term60 A y x s.
Proof. exact (@lem5782650 A y x s). Qed.
Lemma lem5782652 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term60 A y x s) = ((term61 A x y s) = (term62 A y x s)).
Proof. exact (eq_refl (term60 A y x s)). Qed.
Lemma lem5782660 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term63 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5782661 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term63 _120477 _120519 _120521 op) = (term64 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term63 _120477 _120519 _120521 op)). Qed.
Lemma lem5782662 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term64 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5782661 _120477 _120519 _120521 op) (@lem5782660 _120477 _120519 _120521 op)). Qed.
Lemma lem5782663 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5782664 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term65 _120477 _120519 _120521 op.
Proof. exact (@lem5782662 _120477 _120519 _120521 op (@lem5782663 _120519 op h1)). Qed.
Lemma lem5782665 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term66 _120519 _120521 op.
Proof. exact (proj2 (@lem5782664 Prop _120519 _120521 op h1)). Qed.
Lemma lem5782666 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term67 _120519 _120521 op f.
Proof. exact (@lem5782665 _120519 _120521 op h1 f). Qed.
Lemma lem5782667 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term67 _120519 _120521 op f) = (term68 _120519 _120521 op f).
Proof. exact (eq_refl (term67 _120519 _120521 op f)). Qed.
Lemma lem5782668 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term68 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5782667 _120519 _120521 op f) (@lem5782666 _120519 _120521 f op h1)). Qed.
Lemma lem5782669 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term69 _120519 _120521 op f x.
Proof. exact (@lem5782668 _120519 _120521 f op h1 x). Qed.
Lemma lem5782670 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term69 _120519 _120521 op f x) = (term70 _120519 _120521 x op f).
Proof. exact (eq_refl (term69 _120519 _120521 op f x)). Qed.
Lemma lem5782671 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term70 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5782670 _120519 _120521 x op f) (@lem5782669 _120519 _120521 f x op h1)). Qed.
Lemma lem5782672 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term71 _120519 _120521 x op f s.
Proof. exact (@lem5782671 _120519 _120521 x f op h1 s). Qed.
Lemma lem5782673 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term71 _120519 _120521 x op f s) = (term72 _120519 _120521 x op s f).
Proof. exact (eq_refl (term71 _120519 _120521 x op f s)). Qed.
Lemma lem5782674 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term72 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5782673 _120519 _120521 x op s f) (@lem5782672 _120519 _120521 x f s op h1)). Qed.
Lemma lem5782675 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5782676 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term73 _120519 _120521 op x s f) = (term74 _120519 _120521 x op s f).
Proof. exact (@lem5782674 _120519 _120521 x s f op h2 (@lem5782675 _120521 s h1)). Qed.
Lemma lem5782677 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term75 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5782676 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5782678 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term76 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5782677 _120519 _120521 x op f s h0). Qed.
Lemma lem5782680 (p : Prop) (q : Prop) (r : Prop) : (term11 p q r) = (term10 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5782685 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term76 _120519 _120521 x op s f) = (term77 _120519 _120521 x op s f).
Proof. exact (@lem5782680 (@FINITE _120521 s) (@monoidal _120519 op) ((term73 _120519 _120521 op x s f) = (term74 _120519 _120521 x op s f))). Qed.
Lemma lem5782687 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term78 _120477 _120519 op.
Proof. exact (proj1 (@lem5782664 _120477 _120519 Prop op h1)). Qed.
Lemma lem5782688 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term79 _120477 _120519 op f.
Proof. exact (@lem5782687 _120477 _120519 op h1 f). Qed.
Lemma lem5782689 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term79 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term79 _120477 _120519 op f)). Qed.
Lemma lem5782690 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5782689 _120477 _120519 f op) (@lem5782688 _120477 _120519 f op h1)). Qed.
Lemma lem5782696 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5782698 {B : Type'} (R : type1402 B) (op : type1400 B) : (term9 B R op) = ((term9 B R op) = True).
Proof. exact (@lem7 (term9 B R op)). Qed.
Lemma lem5782700 {B : Type'} (x1 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term80 B R op x1.
Proof. exact (@lem5782585 B R op h1 x1). Qed.
Lemma lem5782701 {B : Type'} (R : type1402 B) (x1 : B) (op : type1400 B) : (term80 B R op x1) = (term81 B R x1 op).
Proof. exact (eq_refl (term80 B R op x1)). Qed.
Lemma lem5782702 {B : Type'} (x1 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term81 B R x1 op.
Proof. exact (EQ_MP (@lem5782701 B R x1 op) (@lem5782700 B x1 R op h1)). Qed.
Lemma lem5782703 {B : Type'} (x1 : B) (y1 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term82 B R x1 op y1.
Proof. exact (@lem5782702 B x1 R op h1 y1). Qed.
Lemma lem5782704 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) : (term82 B R x1 op y1) = (term83 B R x1 y1 op).
Proof. exact (eq_refl (term82 B R x1 op y1)). Qed.
Lemma lem5782705 {B : Type'} (x1 : B) (y1 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term83 B R x1 y1 op.
Proof. exact (EQ_MP (@lem5782704 B R x1 y1 op) (@lem5782703 B x1 y1 R op h1)). Qed.
Lemma lem5782706 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term84 B R x1 y1 op x2.
Proof. exact (@lem5782705 B x1 y1 R op h1 x2). Qed.
Lemma lem5782707 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) : (term84 B R x1 y1 op x2) = (term85 B R x1 y1 op x2).
Proof. exact (eq_refl (term84 B R x1 y1 op x2)). Qed.
Lemma lem5782708 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term85 B R x1 y1 op x2.
Proof. exact (EQ_MP (@lem5782707 B R x1 y1 op x2) (@lem5782706 B x1 y1 x2 R op h1)). Qed.
Lemma lem5782709 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term86 B R x1 y1 op x2 y2.
Proof. exact (@lem5782708 B x1 y1 x2 R op h1 y2). Qed.
Lemma lem5782710 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) (y2 : B) : (term86 B R x1 y1 op x2 y2) = (term87 B R x1 y1 op x2 y2).
Proof. exact (eq_refl (term86 B R x1 y1 op x2 y2)). Qed.
Lemma lem5782711 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term87 B R x1 y1 op x2 y2.
Proof. exact (EQ_MP (@lem5782710 B R x1 y1 op x2 y2) (@lem5782709 B x1 y1 x2 y2 R op h1)). Qed.
Lemma lem5782712 {B : Type'} (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term88 B x1 x2 R y1 y2) : term88 B x1 x2 R y1 y2.
Proof. exact (h1). Qed.
Lemma lem5782713 {B : Type'} (op : type1400 B) (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term8 B R op) (h2 : term88 B x1 x2 R y1 y2) : term89 B R x1 y1 op x2 y2.
Proof. exact (@lem5782711 B x1 y1 x2 y2 R op h1 (@lem5782712 B x1 x2 R y1 y2 h2)). Qed.
Lemma lem5782714 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) (y2 : B) : (term89 B R x1 y1 op x2 y2) = ((term89 B R x1 y1 op x2 y2) = True).
Proof. exact (@lem7 (term89 B R x1 y1 op x2 y2)). Qed.
Lemma lem5782715 {B : Type'} (op : type1400 B) (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term8 B R op) (h2 : term88 B x1 x2 R y1 y2) : (term89 B R x1 y1 op x2 y2) = True.
Proof. exact (EQ_MP (@lem5782714 B R x1 y1 op x2 y2) (@lem5782713 B op x1 x2 R y1 y2 h1 h2)). Qed.
Lemma lem5782726 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782727 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem5782726 p q p' q'). Qed.
Lemma lem5782728 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem5782727 p q p'). Qed.
Lemma lem5782729 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : term93 A B R f op g.
Proof. exact (@lem5782728 (term94 A B R f g) (term95 A B R f op g)). Qed.
Lemma lem5782730 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : term96 A B R f op g p'.
Proof. exact (@lem5782729 A B R f op g p'). Qed.
Lemma lem5782731 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : (term96 A B R f op g p') = (term97 A B R f op g p').
Proof. exact (eq_refl (term96 A B R f op g p')). Qed.
Lemma lem5782732 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : term97 A B R f op g p'.
Proof. exact (EQ_MP (@lem5782731 A B R f op g p') (@lem5782730 A B R f op g p')). Qed.
Lemma lem5782733 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : term98 A B R f op g p' q'.
Proof. exact (@lem5782732 A B R f op g p' q'). Qed.
Lemma lem5782734 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : (term98 A B R f op g p' q') = (term99 A B R f op g p' q').
Proof. exact (eq_refl (term98 A B R f op g p' q')). Qed.
Lemma lem5782735 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : term99 A B R f op g p' q'.
Proof. exact (EQ_MP (@lem5782734 A B R f op g p' q') (@lem5782733 A B R f op g p' q')). Qed.
Lemma lem5782763 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term94 A B R f g) = (term94 A B R f g).
Proof. exact (eq_refl (term94 A B R f g)). Qed.
Lemma lem5782764 {A B : Type'} (op : type1400 B) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term100 A B op R f g q'.
Proof. exact (@lem5782735 A B R f op g (term94 A B R f g) q'). Qed.
Lemma lem5782765 {A B : Type'} (op : type1400 B) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term101 A B op R f g q'.
Proof. exact (@lem5782764 A B op R f g q' (@lem5782763 A B R f g)). Qed.
Lemma lem5782780 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term102 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5782690 _120477 _120519 f op h0). Qed.
Lemma lem5782781 {A B : Type'} (f : A -> B) (op : type1400 B) : term102 A B f op.
Proof. exact (@lem5782780 A B f op). Qed.
Lemma lem5782783 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5782696 B op) (@lem5782583 B op h1)). Qed.
Lemma lem5782784 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5782783 B op h1)). Qed.
Lemma lem5782785 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5782784 B op h1) (@lem0)). Qed.
Lemma lem5782786 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (@lem5782781 A B f op (@lem5782785 B op h1)). Qed.
Lemma lem5782787 {B : Type'} (R : type1402 B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem5782788 {A B : Type'} (f : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) : (term103 A B R op f) = (term104 B R op).
Proof. exact (MK_COMB (@lem5782787 B R) (@lem5782786 A B f op h1)). Qed.
Lemma lem5782790 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term102 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5782690 _120477 _120519 f op h0). Qed.
Lemma lem5782791 {A B : Type'} (f : A -> B) (op : type1400 B) : term102 A B f op.
Proof. exact (@lem5782790 A B f op). Qed.
Lemma lem5782792 {A B : Type'} (g : A -> B) (op : type1400 B) : term102 A B g op.
Proof. exact (@lem5782791 A B g op). Qed.
Lemma lem5782794 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5782696 B op) (@lem5782583 B op h1)). Qed.
Lemma lem5782795 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5782794 B op h1)). Qed.
Lemma lem5782796 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5782795 B op h1) (@lem0)). Qed.
Lemma lem5782797 {A B : Type'} (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) g) = (@neutral B op).
Proof. exact (@lem5782792 A B g op (@lem5782796 B op h1)). Qed.
Lemma lem5782798 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) : (term95 A B R f op g) = (term9 B R op).
Proof. exact (MK_COMB (@lem5782788 A B f R op h1) (@lem5782797 A B g op h1)). Qed.
Lemma lem5782800 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term9 B R op) : (term9 B R op) = True.
Proof. exact (EQ_MP (@lem5782698 B R op) (@lem5782586 B R op h1)). Qed.
Lemma lem5782801 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 B R op) : (term95 A B R f op g) = True.
Proof. exact (TRANS (@lem5782798 A B f g R op h1) (@lem5782800 B R op h2)). Qed.
Lemma lem5782802 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 B R op) : term105 A B R f op g.
Proof. exact (fun h0 : term94 A B R f g => @lem5782801 A B f g R op h1 h2). Qed.
Lemma lem5782803 {A B : Type'} (op : type1400 B) (R : type1402 B) (f : A -> B) (g : A -> B) : term106 A B op R f g.
Proof. exact (@lem5782765 A B op R f g True). Qed.
Lemma lem5782804 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 B R op) : (term23 A B R f op g) = (term107 A B R f g).
Proof. exact (@lem5782803 A B op R f g (@lem5782802 A B f g R op h1 h2)). Qed.
Lemma lem5782806 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782807 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term107 A B R f g) = True.
Proof. exact (@lem5782806 (term94 A B R f g)). Qed.
Lemma lem5782808 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 B R op) : (term23 A B R f op g) = True.
Proof. exact (TRANS (@lem5782804 A B f g R op h1 h2) (@lem5782807 A B R f g)). Qed.
Lemma lem5782809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782810 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term9 B R op) : (term25 A B R f op g) = (and True).
Proof. exact (MK_COMB (@lem5782809) (@lem5782808 A B f g R op h1 h2)). Qed.
Lemma lem5782822 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782823 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem5782822 p q p' q'). Qed.
Lemma lem5782824 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem5782823 p q p'). Qed.
Lemma lem5782825 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : term108 A B R f op x s g.
Proof. exact (@lem5782824 (term32 A B R f op g x s) (term36 A B R f op x s g)). Qed.
Lemma lem5782826 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : term109 A B R f op x s g p'.
Proof. exact (@lem5782825 A B R f op x s g p'). Qed.
Lemma lem5782827 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : (term109 A B R f op x s g p') = (term110 A B R f op x s g p').
Proof. exact (eq_refl (term109 A B R f op x s g p')). Qed.
Lemma lem5782828 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : term110 A B R f op x s g p'.
Proof. exact (EQ_MP (@lem5782827 A B R f op x s g p') (@lem5782826 A B R f op x s g p')). Qed.
Lemma lem5782829 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term111 A B R f op x s g p' q'.
Proof. exact (@lem5782828 A B R f op x s g p' q'). Qed.
Lemma lem5782830 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term111 A B R f op x s g p' q') = (term112 A B R f op x s g p' q').
Proof. exact (eq_refl (term111 A B R f op x s g p' q')). Qed.
Lemma lem5782831 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term112 A B R f op x s g p' q'.
Proof. exact (EQ_MP (@lem5782830 A B R f op x s g p' q') (@lem5782829 A B R f op x s g p' q')). Qed.
Lemma lem5782923 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term32 A B R f op g x s) = (term32 A B R f op g x s).
Proof. exact (eq_refl (term32 A B R f op g x s)). Qed.
Lemma lem5782924 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term113 A B R f op g x s q'.
Proof. exact (@lem5782831 A B R f op x s g (term32 A B R f op g x s) q'). Qed.
Lemma lem5782925 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term114 A B R f op g x s q'.
Proof. exact (@lem5782924 A B R f op g x s q' (@lem5782923 A B R f op g x s)). Qed.
Lemma lem5782926 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term32 A B R f op g x s.
Proof. exact (h1). Qed.
Lemma lem5782927 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term30 A x s.
Proof. exact (proj2 (@lem5782926 A B R f op g x s h1)). Qed.
Lemma lem5782928 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : @FINITE A s.
Proof. exact (proj2 (@lem5782927 A B R f op g x s h1)). Qed.
Lemma lem5782929 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5782931 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term115 A x s.
Proof. exact (proj1 (@lem5782927 A B R f op g x s h1)). Qed.
Lemma lem5782932 {A : Type'} (x : A) (s : A -> Prop) : term116 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem5782934 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term27 A B R f op s g.
Proof. exact (proj1 (@lem5782926 A B R f op g x s h1)). Qed.
Lemma lem5782935 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term14 A B s R f g) : term14 A B s R f g.
Proof. exact (h1). Qed.
Lemma lem5782936 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term14 A B s R f g) (h2 : term32 A B R f op g x s) : term15 A B R f op s g.
Proof. exact (@lem5782934 A B R f op g x s h2 (@lem5782935 A B s R f g h1)). Qed.
Lemma lem5782937 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term15 A B R f op s g) = ((term15 A B R f op s g) = True).
Proof. exact (@lem7 (term15 A B R f op s g)). Qed.
Lemma lem5782938 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term14 A B s R f g) (h2 : term32 A B R f op g x s) : (term15 A B R f op s g) = True.
Proof. exact (EQ_MP (@lem5782937 A B R f op s g) (@lem5782936 A B R f op g x s h1 h2)). Qed.
Lemma lem5782947 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782948 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem5782947 p q p' q'). Qed.
Lemma lem5782949 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem5782948 p q p'). Qed.
Lemma lem5782950 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : term117 A B R f op x s g.
Proof. exact (@lem5782949 (term118 A B x s R f g) (term119 A B R f op x s g)). Qed.
Lemma lem5782951 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : term120 A B R f op x s g p'.
Proof. exact (@lem5782950 A B R f op x s g p'). Qed.
Lemma lem5782952 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : (term120 A B R f op x s g p') = (term121 A B R f op x s g p').
Proof. exact (eq_refl (term120 A B R f op x s g p')). Qed.
Lemma lem5782953 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) : term121 A B R f op x s g p'.
Proof. exact (EQ_MP (@lem5782952 A B R f op x s g p') (@lem5782951 A B R f op x s g p')). Qed.
Lemma lem5782954 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term122 A B R f op x s g p' q'.
Proof. exact (@lem5782953 A B R f op x s g p' q'). Qed.
Lemma lem5782955 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term122 A B R f op x s g p' q') = (term123 A B R f op x s g p' q').
Proof. exact (eq_refl (term122 A B R f op x s g p' q')). Qed.
Lemma lem5782956 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term123 A B R f op x s g p' q'.
Proof. exact (EQ_MP (@lem5782955 A B R f op x s g p' q') (@lem5782954 A B R f op x s g p' q')). Qed.
Lemma lem5782964 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782965 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem5782964 p q p' q'). Qed.
Lemma lem5782966 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem5782965 p q p'). Qed.
Lemma lem5782967 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : term124 A B x s R f g x'.
Proof. exact (@lem5782966 (term61 A x' x s) (term125 A B R f g x')). Qed.
Lemma lem5782968 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : term126 A B x s R f g x' p'.
Proof. exact (@lem5782967 A B x s R f g x' p'). Qed.
Lemma lem5782969 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : (term126 A B x s R f g x' p') = (term127 A B x s R f g x' p').
Proof. exact (eq_refl (term126 A B x s R f g x' p')). Qed.
Lemma lem5782970 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : term127 A B x s R f g x' p'.
Proof. exact (EQ_MP (@lem5782969 A B x s R f g x' p') (@lem5782968 A B x s R f g x' p')). Qed.
Lemma lem5782971 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term128 A B x s R f g x' p' q'.
Proof. exact (@lem5782970 A B x s R f g x' p' q'). Qed.
Lemma lem5782972 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : (term128 A B x s R f g x' p' q') = (term129 A B x s R f g x' p' q').
Proof. exact (eq_refl (term128 A B x s R f g x' p' q')). Qed.
Lemma lem5782973 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term129 A B x s R f g x' p' q'.
Proof. exact (EQ_MP (@lem5782972 A B x s R f g x' p' q') (@lem5782971 A B x s R f g x' p' q')). Qed.
Lemma lem5782975 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term61 A x y s) = (term62 A y x s).
Proof. exact (EQ_MP (@lem5782652 A y x s) (@lem5782651 A y x s)). Qed.
Lemma lem5782976 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term61 A x y s) = (term62 A y x s).
Proof. exact (@lem5782975 A y x s). Qed.
Lemma lem5782977 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term61 A x' x s) = (term62 A x x' s).
Proof. exact (@lem5782976 A x x' s). Qed.
Lemma lem5782982 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term130 A B R f g x x' s q'.
Proof. exact (@lem5782973 A B x s R f g x' (term62 A x x' s) q'). Qed.
Lemma lem5782983 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term131 A B R f g x x' s q'.
Proof. exact (@lem5782982 A B R f g x x' s q' (@lem5782977 A x x' s)). Qed.
Lemma lem5782987 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B R f g x') = (term125 A B R f g x').
Proof. exact (eq_refl (term125 A B R f g x')). Qed.
Lemma lem5782988 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : term132 A B x s R f g x'.
Proof. exact (fun h0 : term62 A x x' s => @lem5782987 A B R f g x'). Qed.
Lemma lem5782989 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : term133 A B x s R f g x'.
Proof. exact (@lem5782983 A B R f g x x' s (term125 A B R f g x')). Qed.
Lemma lem5782990 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term134 A B x s R f g x') = (term135 A B x s R f g x').
Proof. exact (@lem5782989 A B x s R f g x' (@lem5782988 A B x s R f g x')). Qed.
Lemma lem5783022 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term136 A B x s R f g) = (term137 A B x s R f g).
Proof. exact (fun_ext (fun x' : A => @lem5782990 A B x s R f g x')). Qed.
Lemma lem5783054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783055 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term118 A B x s R f g) = (term138 A B x s R f g).
Proof. exact (MK_COMB (@lem5783054 A) (@lem5783022 A B x s R f g)). Qed.
Lemma lem5783091 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term139 A B op x s R f g q'.
Proof. exact (@lem5782956 A B R f op x s g (term138 A B x s R f g) q'). Qed.
Lemma lem5783092 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term140 A B op x s R f g q'.
Proof. exact (@lem5783091 A B op x s R f g q' (@lem5783055 A B x s R f g)). Qed.
Lemma lem5783093 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term138 A B x s R f g.
Proof. exact (h1). Qed.
Lemma lem5783094 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term141 A B x s R f g x'.
Proof. exact (@lem5783093 A B x s R f g h1 x'). Qed.
Lemma lem5783095 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term141 A B x s R f g x') = (term135 A B x s R f g x').
Proof. exact (eq_refl (term141 A B x s R f g x')). Qed.
Lemma lem5783096 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term135 A B x s R f g x'.
Proof. exact (EQ_MP (@lem5783095 A B x s R f g x') (@lem5783094 A B x' x s R f g h1)). Qed.
Lemma lem5783097 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (h1 : term62 A x x' s) : term62 A x x' s.
Proof. exact (h1). Qed.
Lemma lem5783098 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (x' : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term62 A x x' s) : term125 A B R f g x'.
Proof. exact (@lem5783096 A B x' x s R f g h1 (@lem5783097 A x x' s h2)). Qed.
Lemma lem5783099 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term125 A B R f g x') = ((term125 A B R f g x') = True).
Proof. exact (@lem7 (term125 A B R f g x')). Qed.
Lemma lem5783100 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (x' : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term62 A x x' s) : (term125 A B R f g x') = True.
Proof. exact (EQ_MP (@lem5783099 A B R f g x') (@lem5783098 A B R f g x x' s h1 h2)). Qed.
Lemma lem5783107 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term77 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5782685 _120519 _120521 x op s f) (@lem5782678 _120519 _120521 x op s f)). Qed.
Lemma lem5783108 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term142 A B x op s f.
Proof. exact (@lem5783107 B A x op s f). Qed.
Lemma lem5783112 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5782929 A s) (@lem5782928 A B R f op g x s h1)). Qed.
Lemma lem5783113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5783114 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term143 A s) = (and True).
Proof. exact (MK_COMB (@lem5783113) (@lem5783112 A B R f op g x s h1)). Qed.
Lemma lem5783116 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5782696 B op) (@lem5782583 B op h1)). Qed.
Lemma lem5783117 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term144 A B s op) = (True /\ True).
Proof. exact (MK_COMB (@lem5783114 A B R f op g x s h2) (@lem5783116 B op h1)). Qed.
Lemma lem5783119 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5783120 : (True /\ True) = True.
Proof. exact (@lem5783119 True). Qed.
Lemma lem5783121 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term144 A B s op) = True.
Proof. exact (TRANS (@lem5783117 A B R f op g x s h1 h2) (@lem5783120)). Qed.
Lemma lem5783122 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : True = (term144 A B s op).
Proof. exact (SYM (@lem5783121 A B R f op g x s h1 h2)). Qed.
Lemma lem5783123 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : term144 A B s op.
Proof. exact (EQ_MP (@lem5783122 A B R f op g x s h1 h2) (@lem0)). Qed.
Lemma lem5783124 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term145 A B op x s f) = (term146 A B x op s f).
Proof. exact (@lem5783108 A B x op s f (@lem5783123 A B R f op g x s h1 h2)). Qed.
Lemma lem5783126 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term147 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5783127 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term148 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5783126 _2963 g t e g' t' e'). Qed.
Lemma lem5783128 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term149 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5783127 _2963 g t e g' t'). Qed.
Lemma lem5783129 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term150 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5783128 _2963 g t e g'). Qed.
Lemma lem5783130 {B : Type'} (g : Prop) (t : B) (e : B) : term150 B g t e.
Proof. exact (@lem5783129 B g t e). Qed.
Lemma lem5783131 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term151 A B x op s f.
Proof. exact (@lem5783130 B (@IN A x s) (@iterate B A op s f) (term152 A B x op s f)). Qed.
Lemma lem5783132 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : term153 A B x op s f g'.
Proof. exact (@lem5783131 A B x op s f g'). Qed.
Lemma lem5783133 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : (term153 A B x op s f g') = (term154 A B x op s f g').
Proof. exact (eq_refl (term153 A B x op s f g')). Qed.
Lemma lem5783134 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : term154 A B x op s f g'.
Proof. exact (EQ_MP (@lem5783133 A B x op s f g') (@lem5783132 A B x op s f g')). Qed.
Lemma lem5783135 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term155 A B x op s f g' t'.
Proof. exact (@lem5783134 A B x op s f g' t'). Qed.
Lemma lem5783136 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : (term155 A B x op s f g' t') = (term156 A B x op s f g' t').
Proof. exact (eq_refl (term155 A B x op s f g' t')). Qed.
Lemma lem5783137 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term156 A B x op s f g' t'.
Proof. exact (EQ_MP (@lem5783136 A B x op s f g' t') (@lem5783135 A B x op s f g' t')). Qed.
Lemma lem5783138 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term157 A B x op s f g' t' e'.
Proof. exact (@lem5783137 A B x op s f g' t' e'). Qed.
Lemma lem5783139 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term157 A B x op s f g' t' e') = (term158 A B x op s f g' t' e').
Proof. exact (eq_refl (term157 A B x op s f g' t' e')). Qed.
Lemma lem5783140 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term158 A B x op s f g' t' e'.
Proof. exact (EQ_MP (@lem5783139 A B x op s f g' t' e') (@lem5783138 A B x op s f g' t' e')). Qed.
Lemma lem5783142 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (@IN A x s) = False.
Proof. exact (@lem5782932 A x s (@lem5782931 A B R f op g x s h1)). Qed.
Lemma lem5783143 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (t' : B) (e' : B) : term159 A B x op s f t' e'.
Proof. exact (@lem5783140 A B x op s f False t' e'). Qed.
Lemma lem5783144 {A B : Type'} (t' : B) (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term160 A B x op s f t' e'.
Proof. exact (@lem5783143 A B x op s f t' e' (@lem5783142 A B R f op g x s h1)). Qed.
Lemma lem5783148 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5783149 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : term161 A B op s f.
Proof. exact (fun h0 : False => @lem5783148 A B op s f). Qed.
Lemma lem5783150 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term162 A B x op s f e'.
Proof. exact (@lem5783144 A B (@iterate B A op s f) e' R f op g x s h1). Qed.
Lemma lem5783151 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term163 A B x op s f e'.
Proof. exact (@lem5783150 A B e' R f op g x s h1 (@lem5783149 A B op s f)). Qed.
Lemma lem5783157 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term152 A B x op s f) = (term152 A B x op s f).
Proof. exact (eq_refl (term152 A B x op s f)). Qed.
Lemma lem5783158 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term164 A B x op s f.
Proof. exact (fun h0 : ~ False => @lem5783157 A B x op s f). Qed.
Lemma lem5783159 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term165 A B x op s f.
Proof. exact (@lem5783151 A B (term152 A B x op s f) R f op g x s h1). Qed.
Lemma lem5783160 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term146 A B x op s f) = (term166 A B x op s f).
Proof. exact (@lem5783159 A B R f op g x s h1 (@lem5783158 A B x op s f)). Qed.
Lemma lem5783162 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5783163 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5783162 B t1 t2). Qed.
Lemma lem5783164 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term166 A B x op s f) = (term152 A B x op s f).
Proof. exact (@lem5783163 B (@iterate B A op s f) (term152 A B x op s f)). Qed.
Lemma lem5783165 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term146 A B x op s f) = (term152 A B x op s f).
Proof. exact (TRANS (@lem5783160 A B R f op g x s h1) (@lem5783164 A B x op s f)). Qed.
Lemma lem5783166 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term145 A B op x s f) = (term152 A B x op s f).
Proof. exact (TRANS (@lem5783124 A B R f op g x s h1 h2) (@lem5783165 A B R f op g x s h2)). Qed.
Lemma lem5783167 {B : Type'} (R : type1402 B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem5783168 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term167 A B R op x s f) = (term168 A B R x op s f).
Proof. exact (MK_COMB (@lem5783167 B R) (@lem5783166 A B R f op g x s h1 h2)). Qed.
Lemma lem5783170 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term77 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5782685 _120519 _120521 x op s f) (@lem5782678 _120519 _120521 x op s f)). Qed.
Lemma lem5783171 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term142 A B x op s f.
Proof. exact (@lem5783170 B A x op s f). Qed.
Lemma lem5783172 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term142 A B x op s g.
Proof. exact (@lem5783171 A B x op s g). Qed.
Lemma lem5783176 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5782929 A s) (@lem5782928 A B R f op g x s h1)). Qed.
Lemma lem5783177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5783178 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term143 A s) = (and True).
Proof. exact (MK_COMB (@lem5783177) (@lem5783176 A B R f op g x s h1)). Qed.
Lemma lem5783180 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5782696 B op) (@lem5782583 B op h1)). Qed.
Lemma lem5783181 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term144 A B s op) = (True /\ True).
Proof. exact (MK_COMB (@lem5783178 A B R f op g x s h2) (@lem5783180 B op h1)). Qed.
Lemma lem5783183 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5783184 : (True /\ True) = True.
Proof. exact (@lem5783183 True). Qed.
Lemma lem5783185 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term144 A B s op) = True.
Proof. exact (TRANS (@lem5783181 A B R f op g x s h1 h2) (@lem5783184)). Qed.
Lemma lem5783186 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : True = (term144 A B s op).
Proof. exact (SYM (@lem5783185 A B R f op g x s h1 h2)). Qed.
Lemma lem5783187 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : term144 A B s op.
Proof. exact (EQ_MP (@lem5783186 A B R f op g x s h1 h2) (@lem0)). Qed.
Lemma lem5783188 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term145 A B op x s g) = (term146 A B x op s g).
Proof. exact (@lem5783172 A B x op s g (@lem5783187 A B R f op g x s h1 h2)). Qed.
Lemma lem5783190 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term147 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5783191 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term148 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5783190 _2963 g t e g' t' e'). Qed.
Lemma lem5783192 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term149 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5783191 _2963 g t e g' t'). Qed.
Lemma lem5783193 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term150 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5783192 _2963 g t e g'). Qed.
Lemma lem5783194 {B : Type'} (g : Prop) (t : B) (e : B) : term150 B g t e.
Proof. exact (@lem5783193 B g t e). Qed.
Lemma lem5783195 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term151 A B x op s g.
Proof. exact (@lem5783194 B (@IN A x s) (@iterate B A op s g) (term152 A B x op s g)). Qed.
Lemma lem5783196 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) : term153 A B x op s g g'.
Proof. exact (@lem5783195 A B x op s g g'). Qed.
Lemma lem5783197 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) : (term153 A B x op s g g') = (term154 A B x op s g g').
Proof. exact (eq_refl (term153 A B x op s g g')). Qed.
Lemma lem5783198 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) : term154 A B x op s g g'.
Proof. exact (EQ_MP (@lem5783197 A B x op s g g') (@lem5783196 A B x op s g g')). Qed.
Lemma lem5783199 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term155 A B x op s g g' t'.
Proof. exact (@lem5783198 A B x op s g g' t'). Qed.
Lemma lem5783200 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : (term155 A B x op s g g' t') = (term156 A B x op s g g' t').
Proof. exact (eq_refl (term155 A B x op s g g' t')). Qed.
Lemma lem5783201 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term156 A B x op s g g' t'.
Proof. exact (EQ_MP (@lem5783200 A B x op s g g' t') (@lem5783199 A B x op s g g' t')). Qed.
Lemma lem5783202 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term157 A B x op s g g' t' e'.
Proof. exact (@lem5783201 A B x op s g g' t' e'). Qed.
Lemma lem5783203 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : (term157 A B x op s g g' t' e') = (term158 A B x op s g g' t' e').
Proof. exact (eq_refl (term157 A B x op s g g' t' e')). Qed.
Lemma lem5783204 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term158 A B x op s g g' t' e'.
Proof. exact (EQ_MP (@lem5783203 A B x op s g g' t' e') (@lem5783202 A B x op s g g' t' e')). Qed.
Lemma lem5783206 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (@IN A x s) = False.
Proof. exact (@lem5782932 A x s (@lem5782931 A B R f op g x s h1)). Qed.
Lemma lem5783207 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) (t' : B) (e' : B) : term159 A B x op s g t' e'.
Proof. exact (@lem5783204 A B x op s g False t' e'). Qed.
Lemma lem5783208 {A B : Type'} (t' : B) (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term160 A B x op s g t' e'.
Proof. exact (@lem5783207 A B x op s g t' e' (@lem5783206 A B R f op g x s h1)). Qed.
Lemma lem5783212 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) : (@iterate B A op s g) = (@iterate B A op s g).
Proof. exact (eq_refl (@iterate B A op s g)). Qed.
Lemma lem5783213 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) : term161 A B op s g.
Proof. exact (fun h0 : False => @lem5783212 A B op s g). Qed.
Lemma lem5783214 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term162 A B x op s g e'.
Proof. exact (@lem5783208 A B (@iterate B A op s g) e' R f op g x s h1). Qed.
Lemma lem5783215 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term163 A B x op s g e'.
Proof. exact (@lem5783214 A B e' R f op g x s h1 (@lem5783213 A B op s g)). Qed.
Lemma lem5783221 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term152 A B x op s g) = (term152 A B x op s g).
Proof. exact (eq_refl (term152 A B x op s g)). Qed.
Lemma lem5783222 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) : term164 A B x op s g.
Proof. exact (fun h0 : ~ False => @lem5783221 A B x op s g). Qed.
Lemma lem5783223 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term165 A B x op s g.
Proof. exact (@lem5783215 A B (term152 A B x op s g) R f op g x s h1). Qed.
Lemma lem5783224 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term146 A B x op s g) = (term166 A B x op s g).
Proof. exact (@lem5783223 A B R f op g x s h1 (@lem5783222 A B x op s g)). Qed.
Lemma lem5783226 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5783227 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5783226 B t1 t2). Qed.
Lemma lem5783228 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term166 A B x op s g) = (term152 A B x op s g).
Proof. exact (@lem5783227 B (@iterate B A op s g) (term152 A B x op s g)). Qed.
Lemma lem5783229 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term146 A B x op s g) = (term152 A B x op s g).
Proof. exact (TRANS (@lem5783224 A B R f op g x s h1) (@lem5783228 A B x op s g)). Qed.
Lemma lem5783230 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term145 A B op x s g) = (term152 A B x op s g).
Proof. exact (TRANS (@lem5783188 A B R f op g x s h1 h2) (@lem5783229 A B R f op g x s h2)). Qed.
Lemma lem5783231 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term32 A B R f op g x s) : (term119 A B R f op x s g) = (term169 A B R f x op s g).
Proof. exact (MK_COMB (@lem5783168 A B R f op g x s h1 h2) (@lem5783230 A B R f op g x s h1 h2)). Qed.
Lemma lem5783233 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term170 B R x1 y1 op x2 y2.
Proof. exact (fun h0 : term88 B x1 x2 R y1 y2 => @lem5782715 B op x1 x2 R y1 y2 h1 h0). Qed.
Lemma lem5783234 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term170 B R x1 y1 op x2 y2.
Proof. exact (@lem5783233 B x1 y1 x2 y2 R op h1). Qed.
Lemma lem5783235 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) : term171 A B R f x op s g.
Proof. exact (@lem5783234 B (f x) (@iterate B A op s f) (g x) (@iterate B A op s g) R op h1). Qed.
Lemma lem5783239 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term172 A B x s R f g x'.
Proof. exact (fun h0 : term62 A x x' s => @lem5783100 A B R f g x x' s h1 h0). Qed.
Lemma lem5783240 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term172 A B x s R f g x'.
Proof. exact (@lem5783239 A B x' x s R f g h1). Qed.
Lemma lem5783241 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term173 A B s R f g x.
Proof. exact (@lem5783240 A B x x s R f g h1). Qed.
Lemma lem5783245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5783246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5783245 A x). Qed.
Lemma lem5783247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5783248 {A : Type'} (x : A) : (term174 A x) = (or True).
Proof. exact (MK_COMB (@lem5783247) (@lem5783246 A x)). Qed.
Lemma lem5783250 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (@IN A x s) = False.
Proof. exact (@lem5782932 A x s (@lem5782931 A B R f op g x s h1)). Qed.
Lemma lem5783251 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term175 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem5783248 A x) (@lem5783250 A B R f op g x s h1)). Qed.
Lemma lem5783253 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5783254 : (True \/ False) = True.
Proof. exact (@lem5783253 False). Qed.
Lemma lem5783255 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : (term175 A x s) = True.
Proof. exact (TRANS (@lem5783251 A B R f op g x s h1) (@lem5783254)). Qed.
Lemma lem5783256 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : True = (term175 A x s).
Proof. exact (SYM (@lem5783255 A B R f op g x s h1)). Qed.
Lemma lem5783257 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term175 A x s.
Proof. exact (EQ_MP (@lem5783256 A B R f op g x s h1) (@lem0)). Qed.
Lemma lem5783258 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : (term125 A B R f g x) = True.
Proof. exact (@lem5783241 A B x s R f g h1 (@lem5783257 A B R f op g x s h2)). Qed.
Lemma lem5783259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5783260 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : (term176 A B R f g x) = (and True).
Proof. exact (MK_COMB (@lem5783259) (@lem5783258 A B R f op g x s h1 h2)). Qed.
Lemma lem5783262 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B R f op g x s) : term177 A B R f op s g.
Proof. exact (fun h0 : term14 A B s R f g => @lem5782938 A B R f op g x s h0 h1). Qed.
Lemma lem5783321 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5783322 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem5783321 p q p' q'). Qed.
Lemma lem5783323 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem5783322 p q p'). Qed.
Lemma lem5783324 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) : term178 A B s R f g _72877.
Proof. exact (@lem5783323 (@IN A _72877 s) (term125 A B R f g _72877)). Qed.
Lemma lem5783325 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) : term179 A B s R f g _72877 p'.
Proof. exact (@lem5783324 A B s R f g _72877 p'). Qed.
Lemma lem5783326 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) : (term179 A B s R f g _72877 p') = (term180 A B s R f g _72877 p').
Proof. exact (eq_refl (term179 A B s R f g _72877 p')). Qed.
Lemma lem5783327 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) : term180 A B s R f g _72877 p'.
Proof. exact (EQ_MP (@lem5783326 A B s R f g _72877 p') (@lem5783325 A B s R f g _72877 p')). Qed.
Lemma lem5783328 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) (q' : Prop) : term181 A B s R f g _72877 p' q'.
Proof. exact (@lem5783327 A B s R f g _72877 p' q'). Qed.
Lemma lem5783329 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) (q' : Prop) : (term181 A B s R f g _72877 p' q') = (term182 A B s R f g _72877 p' q').
Proof. exact (eq_refl (term181 A B s R f g _72877 p' q')). Qed.
Lemma lem5783330 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (p' : Prop) (q' : Prop) : term182 A B s R f g _72877 p' q'.
Proof. exact (EQ_MP (@lem5783329 A B s R f g _72877 p' q') (@lem5783328 A B s R f g _72877 p' q')). Qed.
Lemma lem5783331 {A : Type'} (_72877 : A) (s : A -> Prop) : (@IN A _72877 s) = (@IN A _72877 s).
Proof. exact (eq_refl (@IN A _72877 s)). Qed.
Lemma lem5783332 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (s : A -> Prop) (q' : Prop) : term183 A B R f g _72877 s q'.
Proof. exact (@lem5783330 A B s R f g _72877 (@IN A _72877 s) q'). Qed.
Lemma lem5783333 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (s : A -> Prop) (q' : Prop) : term184 A B R f g _72877 s q'.
Proof. exact (@lem5783332 A B R f g _72877 s q' (@lem5783331 A _72877 s)). Qed.
Lemma lem5783334 {A : Type'} (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : @IN A _72877 s.
Proof. exact (h1). Qed.
Lemma lem5783335 {A : Type'} (_72877 : A) (s : A -> Prop) : (@IN A _72877 s) = ((@IN A _72877 s) = True).
Proof. exact (@lem7 (@IN A _72877 s)). Qed.
Lemma lem5783338 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term172 A B x s R f g x'.
Proof. exact (fun h0 : term62 A x x' s => @lem5783100 A B R f g x x' s h1 h0). Qed.
Lemma lem5783339 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term172 A B x s R f g x'.
Proof. exact (@lem5783338 A B x' x s R f g h1). Qed.
Lemma lem5783340 {A B : Type'} (_72877 : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term172 A B x s R f g _72877.
Proof. exact (@lem5783339 A B _72877 x s R f g h1). Qed.
Lemma lem5783346 {A : Type'} (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : (@IN A _72877 s) = True.
Proof. exact (EQ_MP (@lem5783335 A _72877 s) (@lem5783334 A _72877 s h1)). Qed.
Lemma lem5783347 {A : Type'} (_72877 : A) (x : A) : (term185 A _72877 x) = (term185 A _72877 x).
Proof. exact (eq_refl (term185 A _72877 x)). Qed.
Lemma lem5783348 {A : Type'} (x : A) (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : (term62 A x _72877 s) = (term186 A _72877 x).
Proof. exact (MK_COMB (@lem5783347 A _72877 x) (@lem5783346 A _72877 s h1)). Qed.
Lemma lem5783350 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5783351 {A : Type'} (_72877 : A) (x : A) : (term186 A _72877 x) = True.
Proof. exact (@lem5783350 (_72877 = x)). Qed.
Lemma lem5783352 {A : Type'} (x : A) (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : (term62 A x _72877 s) = True.
Proof. exact (TRANS (@lem5783348 A x _72877 s h1) (@lem5783351 A _72877 x)). Qed.
Lemma lem5783353 {A : Type'} (x : A) (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : True = (term62 A x _72877 s).
Proof. exact (SYM (@lem5783352 A x _72877 s h1)). Qed.
Lemma lem5783354 {A : Type'} (x : A) (_72877 : A) (s : A -> Prop) (h1 : @IN A _72877 s) : term62 A x _72877 s.
Proof. exact (EQ_MP (@lem5783353 A x _72877 s h1) (@lem0)). Qed.
Lemma lem5783355 {A B : Type'} (x : A) (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : @IN A _72877 s) : (term125 A B R f g _72877) = True.
Proof. exact (@lem5783340 A B _72877 x s R f g h1 (@lem5783354 A x _72877 s h2)). Qed.
Lemma lem5783356 {A B : Type'} (_72877 : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term187 A B s R f g _72877.
Proof. exact (fun h0 : @IN A _72877 s => @lem5783355 A B x R f g _72877 s h1 h0). Qed.
Lemma lem5783357 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (_72877 : A) (s : A -> Prop) : term188 A B R f g _72877 s.
Proof. exact (@lem5783333 A B R f g _72877 s True). Qed.
Lemma lem5783358 {A B : Type'} (_72877 : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : (term189 A B s R f g _72877) = (term190 A _72877 s).
Proof. exact (@lem5783357 A B R f g _72877 s (@lem5783356 A B _72877 x s R f g h1)). Qed.
Lemma lem5783360 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5783361 {A : Type'} (_72877 : A) (s : A -> Prop) : (term190 A _72877 s) = True.
Proof. exact (@lem5783360 (@IN A _72877 s)). Qed.
Lemma lem5783362 {A B : Type'} (_72877 : A) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : (term189 A B s R f g _72877) = True.
Proof. exact (TRANS (@lem5783358 A B _72877 x s R f g h1) (@lem5783361 A _72877 s)). Qed.
Lemma lem5783365 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : (term191 A B s R f g) = (term192 A).
Proof. exact (fun_ext (fun _72877 : A => @lem5783362 A B _72877 x s R f g h1)). Qed.
Lemma lem5783366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783367 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : (term14 A B s R f g) = (term193 A).
Proof. exact (MK_COMB (@lem5783366 A) (@lem5783365 A B x s R f g h1)). Qed.
Lemma lem5783369 {A : Type'} (t : Prop) : (term194 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5783370 {A : Type'} (t : Prop) : (term194 A t) = t.
Proof. exact (@lem5783369 A t). Qed.
Lemma lem5783371 {A : Type'} : (term193 A) = True.
Proof. exact (@lem5783370 A True). Qed.
Lemma lem5783372 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : (term14 A B s R f g) = True.
Proof. exact (TRANS (@lem5783367 A B x s R f g h1) (@lem5783371 A)). Qed.
Lemma lem5783373 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : True = (term14 A B s R f g).
Proof. exact (SYM (@lem5783372 A B x s R f g h1)). Qed.
Lemma lem5783374 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term138 A B x s R f g) : term14 A B s R f g.
Proof. exact (EQ_MP (@lem5783373 A B x s R f g h1) (@lem0)). Qed.
Lemma lem5783375 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : (term15 A B R f op s g) = True.
Proof. exact (@lem5783262 A B R f op g x s h2 (@lem5783374 A B x s R f g h1)). Qed.
Lemma lem5783376 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : (term195 A B x R f op s g) = (True /\ True).
Proof. exact (MK_COMB (@lem5783260 A B R f op g x s h1 h2) (@lem5783375 A B R f op g x s h1 h2)). Qed.
Lemma lem5783378 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5783379 : (True /\ True) = True.
Proof. exact (@lem5783378 True). Qed.
Lemma lem5783380 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : (term195 A B x R f op s g) = True.
Proof. exact (TRANS (@lem5783376 A B R f op g x s h1 h2) (@lem5783379)). Qed.
Lemma lem5783381 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : True = (term195 A B x R f op s g).
Proof. exact (SYM (@lem5783380 A B R f op g x s h1 h2)). Qed.
Lemma lem5783382 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term32 A B R f op g x s) : term195 A B x R f op s g.
Proof. exact (EQ_MP (@lem5783381 A B R f op g x s h1 h2) (@lem0)). Qed.
Lemma lem5783383 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term8 B R op) (h3 : term32 A B R f op g x s) : (term169 A B R f x op s g) = True.
Proof. exact (@lem5783235 A B f x s g R op h2 (@lem5783382 A B R f op g x s h1 h3)). Qed.
Lemma lem5783384 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term138 A B x s R f g) (h2 : term8 B R op) (h3 : @monoidal B op) (h4 : term32 A B R f op g x s) : (term119 A B R f op x s g) = True.
Proof. exact (TRANS (@lem5783231 A B R f op g x s h3 h4) (@lem5783383 A B R f op g x s h1 h2 h4)). Qed.
Lemma lem5783385 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term32 A B R f op g x s) : term196 A B R f op x s g.
Proof. exact (fun h0 : term138 A B x s R f g => @lem5783384 A B R f op g x s h0 h1 h2 h3). Qed.
Lemma lem5783386 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : term197 A B op x s R f g.
Proof. exact (@lem5783092 A B op x s R f g True). Qed.
Lemma lem5783387 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term32 A B R f op g x s) : (term36 A B R f op x s g) = (term198 A B x s R f g).
Proof. exact (@lem5783386 A B op x s R f g (@lem5783385 A B R f op g x s h1 h2 h3)). Qed.
Lemma lem5783389 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5783390 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term198 A B x s R f g) = True.
Proof. exact (@lem5783389 (term138 A B x s R f g)). Qed.
Lemma lem5783391 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term32 A B R f op g x s) : (term36 A B R f op x s g) = True.
Proof. exact (TRANS (@lem5783387 A B R f op g x s h1 h2 h3) (@lem5783390 A B x s R f g)). Qed.
Lemma lem5783392 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : term199 A B R f op x s g.
Proof. exact (fun h0 : term32 A B R f op g x s => @lem5783391 A B R f op g x s h1 h2 h0). Qed.
Lemma lem5783393 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : term200 A B R f op g x s.
Proof. exact (@lem5782925 A B R f op g x s True). Qed.
Lemma lem5783394 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term38 A B R f op x s g) = (term201 A B R f op g x s).
Proof. exact (@lem5783393 A B R f op g x s (@lem5783392 A B f x s g R op h1 h2)). Qed.
Lemma lem5783396 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5783397 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term201 A B R f op g x s) = True.
Proof. exact (@lem5783396 (term32 A B R f op g x s)). Qed.
Lemma lem5783398 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term38 A B R f op x s g) = True.
Proof. exact (TRANS (@lem5783394 A B f g x s R op h1 h2) (@lem5783397 A B R f op g x s)). Qed.
Lemma lem5783399 {A B : Type'} (f : A -> B) (x : A) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term40 A B R f op x g) = (term202 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5783398 A B f x s g R op h1 h2)). Qed.
Lemma lem5783400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5783401 {A B : Type'} (f : A -> B) (x : A) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term42 A B R f op x g) = (term203 A).
Proof. exact (MK_COMB (@lem5783400 A) (@lem5783399 A B f x g R op h1 h2)). Qed.
Lemma lem5783403 {A : Type'} (t : Prop) : (term194 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5783404 {A : Type'} (t : Prop) : (term204 A t) = t.
Proof. exact (@lem5783403 (A -> Prop) t). Qed.
Lemma lem5783405 {A : Type'} : (term203 A) = True.
Proof. exact (@lem5783404 A True). Qed.
Lemma lem5783406 {A B : Type'} (f : A -> B) (x : A) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term42 A B R f op x g) = True.
Proof. exact (TRANS (@lem5783401 A B f x g R op h1 h2) (@lem5783405 A)). Qed.
Lemma lem5783407 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term44 A B R f op g) = (term192 A).
Proof. exact (fun_ext (fun x : A => @lem5783406 A B f x g R op h1 h2)). Qed.
Lemma lem5783408 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5783409 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term46 A B R f op g) = (term193 A).
Proof. exact (MK_COMB (@lem5783408 A) (@lem5783407 A B f g R op h1 h2)). Qed.
Lemma lem5783411 {A : Type'} (t : Prop) : (term194 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5783412 {A : Type'} (t : Prop) : (term194 A t) = t.
Proof. exact (@lem5783411 A t). Qed.
Lemma lem5783413 {A : Type'} : (term193 A) = True.
Proof. exact (@lem5783412 A True). Qed.
Lemma lem5783414 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) : (term46 A B R f op g) = True.
Proof. exact (TRANS (@lem5783409 A B f g R op h1 h2) (@lem5783413 A)). Qed.
Lemma lem5783415 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : (term48 A B R f op g) = (True /\ True).
Proof. exact (MK_COMB (@lem5782810 A B f g R op h2 h3) (@lem5783414 A B f g R op h1 h2)). Qed.
Lemma lem5783417 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5783418 : (True /\ True) = True.
Proof. exact (@lem5783417 True). Qed.
Lemma lem5783419 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : (term48 A B R f op g) = True.
Proof. exact (TRANS (@lem5783415 A B f g R op h1 h2 h3) (@lem5783418)). Qed.
Lemma lem5783420 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : True = (term48 A B R f op g).
Proof. exact (SYM (@lem5783419 A B f g R op h1 h2 h3)). Qed.
Lemma lem5783421 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term48 A B R f op g.
Proof. exact (EQ_MP (@lem5783420 A B f g R op h1 h2 h3) (@lem0)). Qed.
Lemma lem5783422 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term19 A B R f op g.
Proof. exact (@lem5782644 A B R f op g (@lem5783421 A B f g R op h1 h2 h3)). Qed.
Lemma lem5783423 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term18 A B R f op g.
Proof. exact (EQ_MP (@lem5782611 A B R f op g) (@lem5783422 A B f g R op h1 h2 h3)). Qed.
Lemma lem5783428 {A B : Type'} (f : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term205 A B R f op.
Proof. exact (fun g : A -> B => @lem5783423 A B f g R op h1 h2 h3). Qed.
Lemma lem5783433 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term206 A B R op.
Proof. exact (fun f : A -> B => @lem5783428 A B f R op h1 h2 h3). Qed.
Lemma lem5783434 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term7 B R op) : term8 B R op.
Proof. exact (proj2 (@lem5782584 B R op h1)). Qed.
Lemma lem5783435 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term7 B R op) : term9 B R op.
Proof. exact (proj1 (@lem5782584 B R op h1)). Qed.
Lemma lem5783436 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : (term8 B R op) = (term206 A B R op).
Proof. exact (prop_ext (fun h4 : term8 B R op => @lem5783433 A B R op h1 h2 h3) (fun h4 : term206 A B R op => @lem5782585 B R op h1)). Qed.
Lemma lem5783437 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term206 A B R op.
Proof. exact (EQ_MP (@lem5783436 A B R op h1 h2 h3) (@lem5782585 B R op h1)). Qed.
Lemma lem5783438 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : (term9 B R op) = (term206 A B R op).
Proof. exact (prop_ext (fun h4 : term9 B R op => @lem5783437 A B R op h1 h2 h3) (fun h4 : term206 A B R op => @lem5782586 B R op h3)). Qed.
Lemma lem5783439 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term8 B R op) (h2 : @monoidal B op) (h3 : term9 B R op) : term206 A B R op.
Proof. exact (EQ_MP (@lem5783438 A B R op h1 h2 h3) (@lem5782586 B R op h3)). Qed.
Lemma lem5783440 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term7 B R op) (h3 : term9 B R op) : (term8 B R op) = (term206 A B R op).
Proof. exact (prop_ext (fun h4 : term8 B R op => @lem5783439 A B R op h4 h1 h3) (fun h4 : term206 A B R op => @lem5783434 B R op h2)). Qed.
Lemma lem5783441 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term7 B R op) (h3 : term9 B R op) : term206 A B R op.
Proof. exact (EQ_MP (@lem5783440 A B R op h1 h2 h3) (@lem5783434 B R op h2)). Qed.
Lemma lem5783442 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term7 B R op) : (term9 B R op) = (term206 A B R op).
Proof. exact (prop_ext (fun h3 : term9 B R op => @lem5783441 A B R op h1 h2 h3) (fun h3 : term206 A B R op => @lem5783435 B R op h2)). Qed.
Lemma lem5783443 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term7 B R op) : term206 A B R op.
Proof. exact (EQ_MP (@lem5783442 A B R op h1 h2) (@lem5783435 B R op h2)). Qed.
Lemma lem5783444 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) : term207 A B R op.
Proof. exact (fun h0 : term7 B R op => @lem5783443 A B R op h1 h0). Qed.
Lemma lem5783449 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term208 A B op.
Proof. exact (fun R : type1402 B => @lem5783444 A B R op h1). Qed.
Lemma lem5783450 {A B : Type'} (op : type1400 B) : term209 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5783449 A B op h0). Qed.
Lemma lem5783455 {A B : Type'} : term210 A B.
Proof. exact (fun op : type1400 B => @lem5783450 A B op). Qed.
